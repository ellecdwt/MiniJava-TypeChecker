// Laura DeWitt
// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
// 
// Static analysis for miniJava (F14) ((A starting version.)
//  1. Type-checking
//  2. Detecting missing return statement
//  3. (Optional) Detecting uninitialized variables
//
// (For CS321 Fall 2014 - Jingke Li)
//

import java.util.*;
import java.io.*;
import ast.*;

public class Checker {

  static class TypeException extends Exception {
    public TypeException(String msg) { super(msg); }
  }

  //------------------------------------------------------------------------------
  // ClassInfo
  //----------
  // For easy access to class hierarchies (i.e. finding parent's info).
  //
  static class ClassInfo {
    Ast.ClassDecl cdecl; 	// classDecl AST
    ClassInfo parent; 		// pointer to parent

    ClassInfo(Ast.ClassDecl cdecl, ClassInfo parent) { 
      this.cdecl = cdecl; 
      this.parent = parent; 
    }      

    // Return the name of this class 
    //
    String className() { return cdecl.nm; }

    // Given a method name, return the method's declaration
    // - if the method is not found in the current class, recursively
    //   search ancestor classes; return null if all fail
    //
    Ast.MethodDecl findMethodDecl(String mname) {
      for (Ast.MethodDecl mdecl: cdecl.mthds)
	if (mdecl.nm.equals(mname))
	  return mdecl;
      if (parent != null)
        return parent.findMethodDecl(mname);
      return null;
    }

    // Given a field name, return the field's declaration
    // - if the field is not found in the current class, recursively
    //   search ancestor classes; return null if all fail
    //
    Ast.VarDecl findFieldDecl(String fname) {
      for (Ast.VarDecl fdecl: cdecl.flds) {
	if (fdecl.nm.equals(fname))
	  return fdecl;
      }
      if (parent != null)
        return parent.findFieldDecl(fname);
      return null;
    }
  }

  //------------------------------------------------------------------------------
  // Global Variables
  // ----------------
  // For type-checking:
  // classEnv - an environment (a className-classInfo mapping) for class declarations
  // typeEnv - an environment (a var-type mapping) for a method's params and local vars
  // thisCInfo - points to the current class's ClassInfo
  // thisMDecl - points to the current method's MethodDecl
  // classObjects - The object is the key and its class is the value
  // returns - stores all returns,if/else,whiles and a bool if they contained a return or not
  // cInit - stores all decalred variables at the class\method scope
  // tempInit - Used to populate above lists and then is temp scope of ifs and whiles
  //
  // For other analyses:
  // (Define as you need.)
  //
  private static HashMap<String, String> classObjects = new HashMap<String, String>();
  private static HashMap<String, ClassInfo> classEnv = new HashMap<String, ClassInfo>();
  private static HashMap<String, Ast.Type> typeEnv = new HashMap<String, Ast.Type>();
  private static ClassInfo thisCInfo = null;
  private static Ast.MethodDecl thisMDecl = null;
  private static List<Pair> returns = new ArrayList<Pair>();
  
  // generic class for pairs of objects
  static class Pair<L,R>{ 
	private final L left;
	private final R right;

    public Pair(L l, R r){
		this.left = l;
		this.right = r;
	}

	public L getLeft(){return left;}
	public R getRight(){return right;}
  }

  // function to run at end of each method to verify return statements
  private static boolean verifyReturns(){
	boolean success = false;
	boolean ifrtn = false;
	boolean nested = false; // if there is a nesting happening
	boolean nestrtn = false; // if both nested have returns
	for(Pair p : returns){
		switch(p.getLeft().toString()){
			case "return":
				success = true;
				break;
			case "while":
				success = (boolean)p.getRight() ? false : true;
				break;
			case "Oif":
			case "Oelse":
				nested = true;
				break;
			case "if":
				if(!(boolean)p.getRight()){
					success = false;
				}
				else if (nested){
					nestrtn = true;
				}
				else{
					ifrtn = true;
				}
				break;
			case "else":
				if(!(boolean)p.getRight()){
					success = false;
				}
				else if(ifrtn){
					success = true;
					ifrtn = false;
				}
				else if(nestrtn){
					ifrtn = true;
				}
				break;
			default:
				break;
		}
	}
	return success;
  }

  //------------------------------------------------------------------------------
  // Type Compatibility Routines
  // ---------------------------

  // Returns true if tsrc is assignable to tdst.
  //
  // Pseudo code:
  //   if tdst==tsrc or both are the same basic type 
  //     return true
  //   else if both are ArrayType // structure equivalence
  //     return assignable result on their element types
  //   else if both are ObjType   // name equivalence 
  //     if (their class names match, or
  //         tdst's class name matches an tsrc ancestor's class name)
  //       return true
  //   else
  //     return false
  //
  private static boolean assignable(Ast.Type tdst, Ast.Type tsrc) throws Exception {
    if (tdst == tsrc
		|| (tdst instanceof Ast.IntType) && (tsrc instanceof Ast.IntType)
		|| (tdst instanceof Ast.BoolType) && (tsrc instanceof Ast.BoolType)) {
      	return true;
    }
	else if ((tdst instanceof Ast.ArrayType) && (tsrc instanceof Ast.ArrayType)){
		Ast.ArrayType dst, src;
		dst = (Ast.ArrayType)tdst;
		src = (Ast.ArrayType)tsrc;
		return assignable(dst.et, src.et);
	}
	else if ((tdst instanceof Ast.ObjType) && (tsrc instanceof Ast.ObjType)){
		Ast.ObjType dst = (Ast.ObjType)tdst;
		Ast.ObjType src = (Ast.ObjType)tsrc;
		if(dst.nm.equals(src.nm)){
			return true;
		}
		else {
			Ast.ClassDecl srcp = classEnv.get(src.nm).cdecl;
			while(srcp.pnm != null){
				if(srcp.pnm.equals(dst.nm)){
					return true;
				}
				else{
					srcp = classEnv.get(srcp.pnm).cdecl;
				}
			}
			return false;
		}
	}
	else {
		return false;
	}
  }
  
  // Returns true if t1 and t2 can be compared with "==" or "!=".
  //
  private static boolean comparable(Ast.Type t1, Ast.Type t2) throws Exception {
    return assignable(t1,t2) || assignable(t2,t1);
  }

  //------------------------------------------------------------------------------
  // The Main Routine
  //-----------------
  //
  public static void main(String [] args) throws Exception {
    try {
      if (args.length == 1) {
        FileInputStream stream = new FileInputStream(args[0]);
        Ast.Program p = new astParser(stream).Program();
        stream.close();
        check(p);
      } else {
	System.out.println("Need a file name as command-line argument.");
      } 
    } catch (TypeException e) {
      System.err.print(e + "\n");
    } catch (Exception e) {
      System.err.print(e + "\n");
    }
  }

  //------------------------------------------------------------------------------
  // Checker Routines for Individual AST Nodes
  //------------------------------------------

  // Program ---
  //  ClassDecl[] classes;
  //
  // 1. Sort ClassDecls, so parent will be visited before children.
  // 2. For each ClassDecl, create a ClassInfo (with link to parent if exists),
  //    and add to classEnv.
  // 3. Actual type-checking traversal over ClassDecls.
  //
  static void check(Ast.Program n) throws Exception {
    Ast.ClassDecl[] classes = topoSort(n.classes);
    for (Ast.ClassDecl c: classes) {
      ClassInfo pcinfo = (c.pnm == null) ? null : classEnv.get(c.pnm);
      classEnv.put(c.nm, new ClassInfo(c, pcinfo));
    }
    for (Ast.ClassDecl c: classes){
      check(c);
	}
  }

  // Utility routine
  // - Sort ClassDecls based on parent-chidren relationship.
  //
  private static Ast.ClassDecl[] topoSort(Ast.ClassDecl[] classes) {
    List<Ast.ClassDecl> cl = new ArrayList<Ast.ClassDecl>();
    Vector<String> done = new Vector<String>();
    int cnt = classes.length;
    while (cnt > 0) {
      for (Ast.ClassDecl cd: classes)
		if (!done.contains(cd.nm)
			&& ((cd.pnm == null) || done.contains(cd.pnm))) {
		  cl.add(cd);
		  done.add(cd.nm);
		  cnt--;
		} 
    }
    return cl.toArray(new Ast.ClassDecl[0]);
  }

  // ClassDecl ---
  //  String nm, pnm;
  //  VarDecl[] flds;
  //  MethodDecl[] mthds;
  //
  //  1. Set thisCInfo pointer to this class's ClassInfo, and reset
  //     typeEnv to empty.
  //  2. Recursively check n.flds and n.mthds.
  //
  static void check(Ast.ClassDecl n) throws Exception {
	Ast.VarDecl[] flds = n.flds.clone();
	Ast.MethodDecl[] mthds = n.mthds.clone();
	thisCInfo = classEnv.get(n.nm);
	typeEnv.clear();
	classObjects.clear();
	for(Ast.VarDecl var : flds){
		typeEnv.put(var.nm, var.t);
		check(var);
	}
	for(Ast.MethodDecl mth : mthds){
		typeEnv.put(mth.nm, mth.t);
		check(mth);
	}
  }

  // MethodDecl ---
  //  Type t;
  //  String nm;
  //  Param[] params;
  //  VarDecl[] vars;
  //  Stmt[] stmts;
  //
  //  1. Set thisMDecl pointer and reset typeEnv to empty.
  //  2. Recursively check n.params, n.vars, and n.stmts.
  //  3. For each VarDecl, add a new name-type binding to typeEnv.
  //
  static void check(Ast.MethodDecl n) throws Exception {
	Ast.Param[] params = n.params.clone();
	Ast.VarDecl[] vars = n.vars.clone();
	Ast.Stmt[] stmts = n.stmts.clone();
	thisMDecl = n;
	typeEnv.clear();
	classObjects.clear();
	returns.clear();
	for(Ast.Param param : params){
		typeEnv.put(param.nm, param.t);
		check(param);
	}
	for(Ast.VarDecl var : vars){
		typeEnv.put(var.nm, var.t);
		check(var);
	}
	for(Ast.Stmt stmt : stmts){
		check(stmt);
		if(stmt instanceof Ast.Return){
			returns.add(new Pair<String,Boolean>("return",true));
		}
	}
	if(n.t != null){
		boolean success = verifyReturns();
		if(!success){
			throw new TypeException("(In MethodDecl) Missing return statement");
		}
	}
  } 

  // Param ---
  //  Type t;
  //  String nm;
  //
  //  If n.t is ObjType, make sure its corresponding class exists.
  //
  static void check(Ast.Param n) throws Exception {
	if(n.t instanceof Ast.ObjType){
		Ast.ObjType clsnm = (Ast.ObjType)n.t;
		if(!classEnv.containsKey(clsnm.nm))
			throw new TypeException("(In Param) Can't find class " + clsnm.nm);
	}
  }

  // VarDecl ---
  //  Type t;
  //  String nm;
  //  Exp init;
  //
  //  1. If n.t is ObjType, make sure its corresponding class exists.
  //  2. If n.init exists, make sure it is assignable to the var.
  //
  static void check(Ast.VarDecl n) throws Exception {
	if(n.t instanceof Ast.ObjType){
		Ast.ObjType clsnm = (Ast.ObjType)n.t;
		if(!classEnv.containsKey(clsnm.nm))
			throw new TypeException("(In VarDecl) Can't find class " + clsnm.nm);
		classObjects.put(n.nm, clsnm.nm);
	}
	if(n.init != null){
		Ast.Type ini = check(n.init);
		if(ini instanceof Ast.ObjType){
			if(!classEnv.containsKey(((Ast.ObjType)ini).nm)){
				throw new TypeException("(In VarDecl) Can't find class " + ((Ast.ObjType)ini).nm);
			}
		}
		if(!assignable(n.t, ini)){
			throw new TypeException("(In VarDecl) rhs cannot be initialized to lhs " + ((Ast.ObjType)ini).nm);
		}
	}
  }

  // STATEMENTS

  // Dispatch a generic check call to a specific check routine
  // 
  static void check(Ast.Stmt n) throws Exception {
    if (n instanceof Ast.Block) 	check((Ast.Block) n);
    else if (n instanceof Ast.Assign)   check((Ast.Assign) n);
    else if (n instanceof Ast.CallStmt) check((Ast.CallStmt) n);
    else if (n instanceof Ast.If) 	check((Ast.If) n);
    else if (n instanceof Ast.While)    check((Ast.While) n);
    else if (n instanceof Ast.Print)    check((Ast.Print) n);
    else if (n instanceof Ast.Return)   check((Ast.Return) n);
    else
      throw new TypeException("(In Stmt) Illegal Ast Stmt: " + n);
  }

  // Block ---
  //  Stmt[] stmts;
  //
  static void check(Ast.Block n) throws Exception {
	for(Ast.Stmt stmt : n.stmts) {
		check(stmt);
	}
  }

  // Assign ---
  //  Exp lhs;
  //  Exp rhs;
  //
  //  Make sure n.rhs is assignable to n.lhs.
  //
  static void check(Ast.Assign n) throws Exception {
	Ast.Type exp1 = check(n.lhs);
	Ast.Type exp2 = check(n.rhs);
	if(exp2 == null){
		return;
	}
	if(!assignable(exp1,exp2)){
		throw new TypeException("(In Assign) lhs and rhs types don't match: " + exp1 + " <- " + exp2); // verify this
	}
  }

  // CallStmt ---
  //  Exp obj; 
  //  String nm;
  //  Exp[] args;
  //
  //  1. Check that n.obj is ObjType and the corresponding class exists.
  //  2. Check that the method n.nm exists.
  //  3. Check that the count and types of the actual arguments match those of
  //     the formal parameters.
  //
  static void check(Ast.CallStmt n) throws Exception {
	if(!((n.obj instanceof Ast.Id)|| (n.obj instanceof Ast.This))){
		throw new TypeException("(In CallStmt) Must be Object type1 " + n.obj);
	}
	if(n.obj instanceof Ast.Id){
		Ast.Id clsnm = (Ast.Id)n.obj;
		if(!(classObjects.containsKey(clsnm.nm))){
			throw new TypeException("(In CallStmt) Class does not exist");
		}
		String cls = classObjects.get(clsnm.nm);
		Ast.MethodDecl mthd = classEnv.get(cls).findMethodDecl(n.nm);
		if(mthd == null){
			throw new TypeException("(In CallStmt) Method does not exist");
		}
		if(mthd.params.length != n.args.length){
			throw new TypeException("(In CallStmt) Param and arg counts don't match: " + mthd.params.length + " vs. " + n.args.length);
		}
		for(int i = 0; i < mthd.params.length; ++i){
			Ast.Type type1 = mthd.params[i].t;
			Ast.Type type2 = check(n.args[i]);
			if(!(type1.getClass().equals(type2.getClass()))){
				throw new TypeException("(In CallStmt) Param and arg types don't match: " + type1 + " vs. " + type2);
			}
			if(type1 instanceof Ast.ObjType){ // make sure object is correct class type
				Ast.ObjType obj1 = (Ast.ObjType)type1;
				Ast.ObjType obj2 = (Ast.ObjType)type2;
				if(classEnv.containsKey(obj1.nm) && classEnv.containsKey(obj2.nm)){
					if(!assignable(obj1,obj2)){
						throw new TypeException("(In CallStmt) Param and arg types don't match: " + type1 + " vs. " + type2);
					}
				}
				else{
				throw new TypeException("(In CallStmt) Class does not exist.");
				}
			}
		}
	}
	else{
		Ast.MethodDecl var = thisCInfo.findMethodDecl(n.nm);
		if(var == null){
			throw new TypeException("(In CallStmt) Can't find method " + n.nm);
		}
		if(var.params.length != n.args.length){
			throw new TypeException("(In CallStmt) Param and arg counts don't match: " + var.params.length + " vs. " + n.args.length);
		}
		for(int i = 0; i < var.params.length; ++i){
			Ast.Type type1 = var.params[i].t;
			Ast.Type type2 = check(n.args[i]);
			if(!(type1.getClass().equals(type2.getClass()))){
				throw new TypeException("(In CallStmt) Param and arg types don't match: " + type1 + " vs. " + type2);
			}
			if(type1 instanceof Ast.ObjType){ // make sure object is correct class type
				Ast.ObjType obj1 = (Ast.ObjType)type1;
				Ast.ObjType obj2 = (Ast.ObjType)type2;
				if(classEnv.containsKey(obj1.nm) && classEnv.containsKey(obj2.nm)){
					if(!assignable(obj1,obj2)){
						throw new TypeException("(In CallStmt) Param and arg types don't match: " + type1 + " vs. " + type2);
					}
				}
				else{
				throw new TypeException("(In CallStmt) Class does not exist.");
				}
			}
		}
	}
  }

  // If ---
  //  Exp cond;
  //  Stmt s1, s2;
  //
  //  Make sure n.cond is boolean.
  //
  static void check(Ast.If n) throws Exception {
	boolean rtn = false;
	boolean nestedIf = false; // true if the if has nested ifs within it
	Ast.Type type = check(n.cond);
	if(!(type instanceof Ast.BoolType)){
		throw new TypeException("(In If) Cond exp type is not boolean: " + type);
	}
	if(n.s1 instanceof Ast.Return){
		returns.add(new Pair<String,Boolean>("if",true));
	}
	else if(n.s1 instanceof Ast.If){
		returns.add(new Pair<String,Boolean>("Oif",false));
	}
	else if(n.s1 instanceof Ast.Block){
		Ast.Block stmt = (Ast.Block)n.s1;
		for (Ast.Stmt s: stmt.stmts) {
      		if(s instanceof Ast.Return){
      			rtn = true;
			}
			else if(s instanceof Ast.If){
      			nestedIf = true;
			}
    	}
		if(rtn){
			returns.add(new Pair<String,Boolean>("if",true));
		}
		else if(nestedIf){
			returns.add(new Pair<String,Boolean>("Oif",false));
		}
		else{
			returns.add(new Pair<String,Boolean>("if",false));
		}
	}
	else{
		returns.add(new Pair<String,Boolean>("if",false));
	}
	check(n.s1);
	if(n.s2 != null){
		rtn = false; //reset for next test
		nestedIf = false; // reset for next test
		if(n.s2 instanceof Ast.Return){
			returns.add(new Pair<String,Boolean>("else",true));
		}
		else if(n.s1 instanceof Ast.If){
		returns.add(new Pair<String,Boolean>("Oelse",false));
		}
		else if(n.s2 instanceof Ast.Block){
			Ast.Block stmt = (Ast.Block)n.s2;
			for (Ast.Stmt s: stmt.stmts) {
      			if(s instanceof Ast.Return){
      				rtn = true;
					break;
				}
				else if(s instanceof Ast.If){
      				nestedIf = true;
				}
			}
			if(rtn){
				returns.add(new Pair<String,Boolean>("if",true));
			}
			else if(nestedIf){
				returns.add(new Pair<String,Boolean>("Oelse",false));
			}
			else{
				returns.add(new Pair<String,Boolean>("if",false));
			}
		}
		else{
			returns.add(new Pair<String,Boolean>("else",false));
		}
		check(n.s2);
	}
  }

  // While ---
  //  Exp cond;
  //  Stmt s;
  //
  //  Make sure n.cond is boolean.
  //
  static void check(Ast.While n) throws Exception {
	Ast.Type type = check(n.cond);
	if(!(type instanceof Ast.BoolType)){
		throw new TypeException("(In While) Cond exp type is not boolean: " + type);
	}
	if(n.s instanceof Ast.Return){
		returns.add(new Pair<String,Boolean>("while",true));
	}
	else if(n.s instanceof Ast.Block){
		Ast.Block stmt = (Ast.Block)n.s;
		for (Ast.Stmt st: stmt.stmts) {
      		if(st instanceof Ast.Return){
      			returns.add(new Pair<String,Boolean>("while",true));
			}
    	}
	}
	check(n.s);
  }
  
  // Print ---
  //  PrArg arg;
  //
  //  Make sure n.arg is integer, boolean, or string.
  //
  static void check(Ast.Print n) throws Exception {
	if (n.arg == null){
		return;
	}
	if(n.arg.toString().matches("\"(.*)\"")){
		return;
	}
	Ast.Exp args = (Ast.Exp)n.arg;	
	Ast.Type type = check(args);
	if(!((type instanceof Ast.IntType) || (type instanceof Ast.BoolType))){
		throw new TypeException("(In Print) Arg type is not int, boolean, or string: " + type);
	}
  }

  // Return ---  
  //  Exp val;
  //
  //  If n.val exists, make sure it matches the expected return type.
  //
  static void check(Ast.Return n) throws Exception {
	if((n.val == null && thisMDecl.t != null)){
		throw new TypeException("(In Return) Missing return value of type " + thisMDecl.t);
	}
	else if((n.val != null && thisMDecl.t == null)){
		throw new TypeException("(In Return) Unexpected return value");
	}
	if(n.val == null && thisMDecl.t == null){
		return;
	}
	Ast.Type rtn = check(n.val);
	if(!rtn.getClass().equals(thisMDecl.t.getClass())){
		throw new TypeException("(In Return) Return type mismatch: " + thisMDecl.t + " <- " + rtn);
	}
  }

  // EXPRESSIONS

  // Dispatch a generic check call to a specific check routine
  //
  static Ast.Type check(Ast.Exp n) throws Exception {
    if (n instanceof Ast.Binop)    return check((Ast.Binop) n);
    if (n instanceof Ast.Unop)     return check((Ast.Unop) n);
    if (n instanceof Ast.Call)     return check((Ast.Call) n);
    if (n instanceof Ast.NewArray) return check((Ast.NewArray) n);
    if (n instanceof Ast.ArrayElm) return check((Ast.ArrayElm) n);
    if (n instanceof Ast.NewObj)   return check((Ast.NewObj) n);
    if (n instanceof Ast.Field)    return check((Ast.Field) n);
    if (n instanceof Ast.Id)	   return check((Ast.Id) n);
    if (n instanceof Ast.This)     return check((Ast.This) n);
    if (n instanceof Ast.IntLit)   return check((Ast.IntLit) n);
    if (n instanceof Ast.BoolLit)  return check((Ast.BoolLit) n);
    throw new TypeException("(In Exp) Exp node not recognized: " + n);
  }

  // Binop ---
  //  BOP op;
  //  Exp e1,e2;
  //
  //  Make sure n.e1's and n.e2's types are legal with respect to n.op.
  //
  static Ast.Type check(Ast.Binop n) throws Exception {
	Ast.Type e1 = check(n.e1);
	Ast.Type e2 = check(n.e2);
	if (comparable(e1,e2)){
		switch(n.op){
			case ADD:
			case SUB:
			case MUL:
			case DIV:
				if(e1 instanceof Ast.IntType)
					return new Ast.IntType();
				throw new TypeException("(In Binop) Bad operand types for binary operator: " + n.op);
			case AND:
			case OR:
				if(e1 instanceof Ast.IntType)
					throw new TypeException("(In Binop) Bad operand types for binary operator: " + n.op);
			default:
				return new Ast.BoolType();
		}
	}
	else {
		throw new TypeException("(In Binop) Operand types don't match: " + e1 + " " + n.op + " " + e2);
	}
  }
   
  // Unop ---
  //  UOP op;
  //  Exp e;
  //
  //  Make sure n.e's type is legal with respect to n.op.
  //
  static Ast.Type check(Ast.Unop n) throws Exception {
	if(!(n.e instanceof Ast.IntLit || n.e instanceof Ast.BoolLit)){
		Ast.Type type = check(n.e);
		if(type instanceof Ast.IntType){
			if(n.op.equals(Ast.UOP.NEG)){
				return new Ast.IntType ();
			}
			else{
				throw new TypeException("(In Unop) Bad operand type: " + n.op + " " + type);
			}
		}
		else if(type instanceof Ast.BoolType){
			if(n.op.equals(Ast.UOP.NOT)){
				return new Ast.BoolType();
			}
			else{
				throw new TypeException("(In Unop) Bad operand type: " + n.op + " BoolType" );
			}
		}
	}
	else if(n.e instanceof Ast.IntLit){
		if(n.op.equals(Ast.UOP.NEG)){
			return new Ast.IntType ();
		}
		else{
			throw new TypeException("(In Unop) Bad operand type: " + n.op + " IntType");
		}
	}
	else if(n.e instanceof Ast.BoolLit){
		if(n.op.equals(Ast.UOP.NOT)){
			return new Ast.BoolType();
		}
		else{
			throw new TypeException("(In Unop) Bad operand type: " + n.op + " BoolType");
		}
	}
	throw new TypeException("(In Unop) Type is not integer or boolean"); // should never reach this
  }
  
  // Call ---
  //  Exp obj; 
  //  String nm;
  //  Exp[] args;
  //
  //  1. Check that n.obj is ObjType and the corresponding class exists.
  //  2. Check that the method n.nm exists.
  //  3. Check that the count and types of the actual arguments match those of
  //     the formal parameters.
  //  In addition, this routine needs to return the method's return type.
  //  
  static Ast.Type check(Ast.Call n) throws Exception {
	if(!((n.obj instanceof Ast.Id) || (n.obj instanceof Ast.This))){
		throw new TypeException("(In Call) Not an object type: " + n.obj);
	}
	if(n.obj instanceof Ast.Id){
		Ast.Id clsnm = (Ast.Id)n.obj;
		if(!(classObjects.containsKey(clsnm.nm))){
			throw new TypeException("(In Call) Class does not exist: " + clsnm.nm);
		}
		String cls = classObjects.get(clsnm.nm);
		Ast.MethodDecl mthd = classEnv.get(cls).findMethodDecl(n.nm);
		if(mthd == null){
			throw new TypeException("(In Call) Method does not exist: " + n.nm);
		}
		if(mthd.params.length != n.args.length){
			throw new TypeException("(In Call) Param and arg counts don't match: " + mthd.params.length + " vs. " + n.args.length);
		}
		for(int i = 0; i < mthd.params.length; ++i){
			Ast.Type type1 = mthd.params[i].t;
			Ast.Type type2 = check(n.args[i]);
			if(!(type1.getClass().equals(type2.getClass()))){
				throw new TypeException("(In Call) Param and arg types don't match: " + type1 + " vs. " + type2);
			}
			if(type1 instanceof Ast.ObjType){ // make sure object is correct class type
				Ast.ObjType obj1 = (Ast.ObjType)type1;
				Ast.ObjType obj2 = (Ast.ObjType)type2;
				if(classEnv.containsKey(obj1.nm) && classEnv.containsKey(obj2.nm)){
					if(!assignable(obj1,obj2)){
						throw new TypeException("(In Call) Param and arg types don't match: " + type1 + " vs. " + type2);
					}
				}
				else{
				throw new TypeException("(In Call) Class does not exist.");
				}
			}
		}
		return mthd.t;
	}
	else{
		Ast.MethodDecl var = thisCInfo.findMethodDecl(n.nm);
		if(var == null){
			throw new TypeException("(In Call) Can't find method " + n.nm);
		}
		if(var.params.length != n.args.length){
			throw new TypeException("(In Call) Param and arg counts don't match: " + var.params.length + " vs. " + n.args.length);
		}
		for(int i = 0; i < var.params.length; ++i){
			Ast.Type type1 = var.params[i].t;
			Ast.Type type2 = check(n.args[i]);
			if(!(type1.getClass().equals(type2.getClass()))){
				throw new TypeException("(In Call) Param and arg types don't match: " + type1 + " vs. " + type2);
			}
			if(type1 instanceof Ast.ObjType){ // make sure object is correct class type
				Ast.ObjType obj1 = (Ast.ObjType)type1;
				Ast.ObjType obj2 = (Ast.ObjType)type2;
				if(classEnv.containsKey(obj1.nm) && classEnv.containsKey(obj2.nm)){
					if(!assignable(obj1,obj2)){
						throw new TypeException("(In Call) Param and arg types don't match: " + type1 + " vs. " + type2);
					}
				}
				else{
				throw new TypeException("(In Call) Class does not exist.");
				}
			}
		}
		return var.t;
	}
  }

  // NewArray ---
  //  Type et;
  //  int len;
  //
  //  1. Verify that n.et is either integer or boolean.
  //  2. Verify that n.len is non-negative. 
  //  (Note: While the AST representation allows these cases to happen, our 
  //  miniJava parser does not, so these checks are not very meaningful.)
  //
  static Ast.Type check(Ast.NewArray n) throws Exception {
	if(n.et instanceof Ast.IntType || n.et instanceof Ast.BoolType){
		if(n.len >= 0){
			return new Ast.ArrayType(n.et);
		}
		else{
			throw new TypeException("(In NewArray) Index cannot be negative");
		}
	}
	else{
		throw new TypeException("(In NewArray) Type is not integer or boolean");
	}
  }

  // ArrayElm ---
  //  Exp ar, idx;
  //
  //  Verify that n.ar is array and n.idx is integer.
  //
  static Ast.Type check(Ast.ArrayElm n) throws Exception {
	if(!(n.ar instanceof Ast.Id)){
		throw new TypeException("(In ArrayElm) Must be Id exp");
	}
	Ast.Id objnm = (Ast.Id)n.ar;
	if(!(typeEnv.containsKey(objnm.nm))){
		Ast.VarDecl var = thisCInfo.findFieldDecl(objnm.nm);
		if(var == null){
			throw new TypeException("(In ArrayElm) Array does not exist " + objnm.nm + " " + n.ar + " " + n.idx);
		}
		else{
			if(!(var.t instanceof Ast.ArrayType)){
				throw new TypeException("(In ArrayElm) Array does not exist");
			}
			if(!(n.idx instanceof Ast.IntLit)){
				Ast.Type index = check(n.idx);
				if(index instanceof Ast.IntType){
					return index;
				}
				else {
					throw new TypeException("(In ArrayElm) Index is not integer: " + check(n.idx));
				}
			}
			else{
				return new Ast.IntType();
			}
		}
	}
	else {
		if(!(typeEnv.get(objnm.nm) instanceof Ast.ArrayType)) {	
			throw new TypeException("(In ArrayElm) Object is not array: " + typeEnv.get(objnm.nm));
		}
		if(!(n.idx instanceof Ast.IntLit)){
			Ast.Type index = check(n.idx);
			if(index instanceof Ast.IntType){
				return index;
			}
			else {
				throw new TypeException("(In ArrayElm) Index is not integer: " + check(n.idx));
			}
		}
		else{
			return new Ast.IntType();
		}
	}
  }

  // NewObj ---
  //  String nm;
  //
  //  Verify that the corresponding class exists.
  //
  static Ast.Type check(Ast.NewObj n) throws Exception {
	if(classEnv.containsKey(n.nm)){
		return new Ast.ObjType(n.nm);
	}
	else{
		throw new TypeException("(In NewObj) Can't find class " + n.nm);
	}
  }
  
  // Field ---
  //  Exp obj; 
  //  String nm;
  //
  //  1. Verify that n.obj is ObjType, and its corresponding class exists.
  //  2. Verify that n.nm is a valid field in the object.
  //
  static Ast.Type check(Ast.Field n) throws Exception {
	if(!((n.obj instanceof Ast.Id) || (n.obj instanceof Ast.This) || (n.obj instanceof Ast.Field))){
		throw new TypeException("(In Field) Object is not ObjectType: " + n.obj);
	}
	if(n.obj instanceof Ast.Id){
		Ast.Id clsnm = (Ast.Id)n.obj;
		if(!typeEnv.containsKey(clsnm.nm)){
			throw new TypeException("(In Field) Object has not been declared: " + clsnm.nm);
		}
		Ast.Type type = typeEnv.get(clsnm.nm);
		if(!(type instanceof Ast.ObjType)){
			throw new TypeException("(In Field) Object is not of ObjType: " + type);
		}
		if(!(classObjects.containsKey(clsnm.nm))){
			throw new TypeException("(In Field) Object class does not exisit: " + clsnm.nm);
		}
		if(classEnv.get(classObjects.get(clsnm.nm)).findFieldDecl(n.nm) != null){
			return classEnv.get(classObjects.get(clsnm.nm)).findFieldDecl(n.nm).t;
		}
		throw new TypeException("(In Field) Can't find field " + n.nm);
	}
	else if(n.obj instanceof Ast.Field){
		Ast.Type next = check(n.obj);
		if(!(next instanceof Ast.ObjType)){
			throw new TypeException("(In Field) Object is not of ObjType: " + next);
		}
		Ast.ObjType temp = (Ast.ObjType)next;
		if(!(classEnv.containsKey(temp.nm))){
			throw new TypeException("(In Field) Object class does not exisit: " + temp.nm);
		}
		if(classEnv.get(temp.nm).findFieldDecl(n.nm) != null){
			return classEnv.get(temp.nm).findFieldDecl(n.nm).t;
		}
		throw new TypeException("(In Field) Can't find field " + n.nm);
	}
	else{
		Ast.VarDecl var = thisCInfo.findFieldDecl(n.nm);
		if(var == null){
			throw new TypeException("(In Field) field not in class");
		}
		return var.t;
	}
  }
  
  // Id ---
  //  String nm;
  //
  //  1. Check if n.nm is in typeEnv. If so, the Id is a param or a local var.
  //     Obtain and return its type.
  //  2. Otherwise, the Id is a field variable. Find and return its type (through
  //     the current ClassInfo).
  //
  static Ast.Type check(Ast.Id n) throws Exception {
	if(typeEnv.containsKey(n.nm)){
		return typeEnv.get(n.nm);
	}
	else{
		Ast.VarDecl temp = thisCInfo.findFieldDecl(n.nm);
		if(temp == null){
			throw new TypeException("(In Id) Can't find variable " + n.nm);
		}
		return temp.t;
	}
  }

  // This ---
  //
  //  Find and return an ObjType that corresponds to the current class
  //  (through the current ClassInfo).
  //
  static Ast.Type check(Ast.This n) {
	String name = thisCInfo.className();
	return typeEnv.get(name);
  }

  // Literals
  //
  public static Ast.Type check(Ast.IntLit n) { 
    return Ast.IntType; 
  }

  public static Ast.Type check(Ast.BoolLit n) { 
    return Ast.BoolType; 
  }

  public static void check(Ast.StrLit n) {
    // nothing to check or return
  }

}
