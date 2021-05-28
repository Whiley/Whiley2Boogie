// Copyright 2020 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wyboogie.tasks;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static wyboogie.core.BoogieFile.*;
import static wyboogie.util.Util.*;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.LVal;

import wyboogie.util.AbstractExpressionTransform;
import wyboogie.util.DefinednessExtractor;
import wybs.lang.Build;
import wybs.lang.Build.Meter;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractCompilationUnit.Tuple;
import wyfs.util.Pair;
import wyil.lang.WyilFile;
import wyil.util.AbstractVisitor;
import wyil.util.AbstractTranslator;
import wyil.util.IncrementalSubtypingEnvironment;
import wyil.util.Subtyping;
import wyil.util.TypeMangler;
import wyil.util.WyilUtils;

public class BoogieCompiler extends AbstractTranslator<Decl, Stmt, Expr> {
    /**
     * Provides a standard mechanism for writing out type mangles.
     */
    private final static TypeMangler mangler = new TypeMangler.Default();

    /**
     * Provides a standard mechanism for checking whether two Whiley types are subtypes or not.
     */
    private final static Subtyping.Environment subtyping = new IncrementalSubtypingEnvironment();

    private final BoogieFile boogieFile;

    /**
     * Flag to signal whether or not to apply mangling.  By default this is enabled.
     */
    private boolean mangling;

    public BoogieCompiler(Meter meter, BoogieFile target) {
        super(meter, subtyping);
        this.boogieFile = target;
        this.mangling = true;
    }

    /**
     * Enable or disable name mangling.  For example, it is useful to disable mangling when debugging.
     * @param flag
     */
    public void setMangling(boolean flag) {
        this.mangling = flag;
    }

    public void visitModule(WyilFile wf) {
        // Add general axioms
        boogieFile.getDeclarations().addAll(constructAxioms(wf));
        // Translate local units
        for (WyilFile.Decl.Unit unit : wf.getModule().getUnits()) {
            for (WyilFile.Decl decl : unit.getDeclarations()) {
                BoogieFile.Decl d = visitDeclaration(decl);
                if (d != null) {
                    boogieFile.getDeclarations().add(d);
                }
            }
        }
        // Translate non-local units
        for (WyilFile.Decl.Unit unit : wf.getModule().getExterns()) {
            for (WyilFile.Decl decl : unit.getDeclarations()) {
                BoogieFile.Decl d = visitDeclaration(decl);
                if (d != null) {
                    boogieFile.getDeclarations().add(d);
                }
            }
        }
    }

    @Override
    public Decl constructImport(WyilFile.Decl.Import d) {
        return new Decl.Sequence();
    }

    @Override
    public Decl constructType(WyilFile.Decl.Type d, List invariant) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Instantiation each one
        decls.addAll(constructConcreteType(d, d.getType(), invariant));
        // Done!
        return new Decl.Sequence(decls);
    }

    /**
     * Construct all the necessary helpers and aliases the are necessary for representing a given Whiley type in Boogie.
     * This is slightly complicated by the fact that we may want multiple instantiations of a given (generic) type.
     *
     * @param decl
     * @param instantiation
     * @param invariant
     * @return
     */
    private List<Decl> constructConcreteType(WyilFile.Decl.Type decl, WyilFile.Type instantiation, List<Expr.Logical> invariant) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Extract template
        Tuple<WyilFile.Template.Variable> template = decl.getTemplate();
        // Add helpful comment
        decls.addAll(constructCommentHeading(decl.getQualifiedName() + " : " + instantiation));
        WyilFile.Decl.Variable var = decl.getVariableDeclaration();
        // Convert the Whiley type into a Boogie type
        Type type = constructType(var.getType());
        // Determine mangled name for type declaration
        String name = toMangledName(decl, instantiation);
        // Create an appropriate synonym
        decls.add(new Decl.TypeSynonym(name, type));
        // Determine the (mangled) variable name
        String varName = toVariableName(var);
        // Create invariant
        ArrayList<Decl.Parameter> parameters = new ArrayList<>();
        ArrayList<Expr> arguments = new ArrayList<>();
        for (int i = 0; i != template.size(); ++i) {
            WyilFile.Template.Variable T = template.get(i);
            parameters.add(new Decl.Parameter(T.getName().get(), TYPE));
            arguments.add(VAR(T.getName().get()));
        }
        parameters.add(new Decl.Parameter(varName, type));
        arguments.add(unbox(var.getType(), VAR(varName)));
        parameters.add(HEAP_PARAM);
        arguments.add(HEAP);
        Expr inv = AND(invariant);
        decls.add(FUNCTION(name + "#inv", parameters, Type.Bool, inv));
        // Generate test for the type itself
        Expr.Logical test = constructTypeTest(instantiation, WyilFile.Type.Any, VAR(varName), HEAP, decl.getType());
        test = AND(test, INVOKE(name + "#inv", arguments));
        parameters.set(template.size(), new Decl.Parameter(varName, ANY));
        decls.add(FUNCTION(name + "#is", parameters, Type.Bool, test));
        // Done
        return decls;
    }

    @Override
    public Decl constructStaticVariable(WyilFile.Decl.StaticVariable d, Expr initialiser) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentHeading("STATIC: " + d.getQualifiedName()));
        Type type = constructType(d.getType());
        // Apply name mangling
        String name = toMangledName(d);
        // Final static variables declared as constants with corresponding axiom
        decls.add(new Decl.Constant(name, type));
        if (initialiser != null) {
            Expr rhs = cast(d.getType(), d.getInitialiser().getType(), initialiser);
            decls.add(new Decl.Axiom(EQ(VAR(name), rhs)));
            // Add type invariant guarantee
            decls.add(new Decl.Axiom(IMPLIES(GT(VAR("Context#Level"), CONST(1)), constructTypeTest(d.getType(), VAR(name), EMPTY_HEAPVAR, d))));
            decls.addAll(constructStaticVariableCheck(d));
            // Add any lambda's used within the function
            decls.addAll(constructLambdas(d));
        }
        return new Decl.Sequence(decls);
    }

    /**
     * Construct an appropriate check that a given initialiser meets any invariants imposed by the static variable's type.
     *
     * @param d
     * @return
     */
    private List<Decl> constructStaticVariableCheck(WyilFile.Decl.StaticVariable d) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Apply name mangling
        String name = toMangledName(d);
        // Construct precondition to prevents axiom firing trivially
        List<Expr.Logical> precondition = Arrays.asList(EQ(VAR("Context#Level"),CONST(1)));
        // Construct simple assertion for the body
        Stmt body = SEQUENCE(ASSERT(constructTypeTest(d.getType(), VAR(name), EMPTY_HEAPVAR, d), ATTRIBUTE(d.getInitialiser()), ATTRIBUTE(WyilFile.STATIC_TYPEINVARIANT_FAILURE)));
        // Construct the checking method method
        decls.add(new Decl.Procedure(name + "#check", Collections.EMPTY_LIST, Collections.EMPTY_LIST, precondition, Collections.EMPTY_LIST, Collections.EMPTY_LIST, Collections.EMPTY_LIST, body));
        // Done
        return decls;
    }

    @Override
    public Decl constructProperty(WyilFile.Decl.Property d, List clauses) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentHeading("PROPERTY: " + d.getQualifiedName()));
        // Apply name mangling
        String name = toMangledName(d);
        // Construct parameters
        Pair<List<Decl.Parameter>, List<Expr.Logical>> parameters = constructParameters(d.getTemplate(), d.getParameters(), HEAP);
        // FIXME: what to do with the type constraints?
        decls.add(FUNCTION(name, append(HEAP_PARAM, parameters.first()), Type.Bool, AND(clauses)));
        return new Decl.Sequence(decls);
    }

    @Override
    public Decl constructFunction(WyilFile.Decl.Function d, List<Expr> precondition, List<Expr> postcondition,
                                  Stmt body) {
        return constructFunctionOrMethod(d, precondition, postcondition, body);
    }

    @Override
    public Decl constructMethod(WyilFile.Decl.Method d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
        return constructFunctionOrMethod(d, precondition, postcondition, body);
    }

    private Decl constructFunctionOrMethod(WyilFile.Decl.FunctionOrMethod d, List<Expr> precondition, List<Expr> postcondition, Stmt body) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Apply name mangling
        String name = toMangledName(d);
        // Determine concrete instantiations of this function
        Pair<List<Decl.Parameter>, List<Expr.Logical>> parametersAndConstraints = constructParameters(d.getTemplate(), d.getParameters(), HEAP);
        Pair<List<Decl.Parameter>, List<Expr.Logical>> returnsAndConstraints = constructParameters(null, d.getReturns(), HEAP);
        // Extract parameter and returns
        List<Decl.Parameter> params = parametersAndConstraints.first();
        List<Decl.Parameter> returns = returnsAndConstraints.first();
        // Merge preconditions / postconditions
        List<Expr.Logical> requires = append(parametersAndConstraints.second(), flatternAsLogical(precondition));
        List<Expr.Logical> ensures = append(returnsAndConstraints.second(), flatternAsLogical(postcondition));
        // Add useful comment
        decls.addAll(constructCommentHeading(d.getQualifiedName() + " : " + d.getType()));
        // Add method prototype
        decls.addAll(constructProcedurePrototype(d, name, params, returns, requires, ensures));
        // Add any lambda's used within the method
        decls.addAll(constructLambdas(d));
        // Add implementation (if one exists)
        if(d.getBody().size() > 0) {
            // Yes, this is not an external symbol
            decls.addAll(constructProcedureImplementation(d, name, params, returns, requires, ensures, body));
        }
        // Done
        return new Decl.Sequence(decls);
    }

    public List<Decl> constructProcedurePrototype(WyilFile.Decl.FunctionOrMethod d, String name, List<Decl.Parameter> params, List<Decl.Parameter> returns, List<Expr.Logical> requires, List<Expr.Logical> ensures) {
        List<String> modifies = Collections.EMPTY_LIST;
        ArrayList<Decl> decls = new ArrayList<>();
        ArrayList<Expr.Logical> freeRequires = new ArrayList<>();
        ArrayList<Expr.Logical> freeEnsures = new ArrayList<>();
        // Add Context Level Guarantee
        requires.add(GT(VAR("Context#Level"), CONST(1)));
        // Apply method-specific stuff
        if(d instanceof WyilFile.Decl.Method) {
            // Add type invariant preservation guarantee
            ensures.addAll(constructMethodFrame((WyilFile.Decl.Method) d));
            // Methods always modify the heap
            modifies = Arrays.asList("HEAP");
        } else {
            ArrayList<Decl.Parameter> f_params = new ArrayList<>(params);
            f_params.add(0,HEAP_PARAM);
            List<Expr> f_args = map(f_params, p -> VAR(p.getName()));
            List<Expr> f_rets = map(returns, p -> VAR(p.getName()));
            // Add function prototype
            switch (d.getReturns().size()) {
                case 0:
                    decls.add(FUNCTION(name, f_params, ANY));
                    break;
                case 1: {
                    Type returnType = returns.get(0).getType();
                    decls.add(FUNCTION(name, f_params, returnType));
                    // Establish connection
                    freeEnsures.add(EQ(INVOKE(name,f_args),f_rets.get(0)));
                    break;
                }
                default: {
                    // Multiple returns require special handling
                    for (int i = 0; i != returns.size(); ++i) {
                        Type returnType = returns.get(i).getType();
                        decls.add(FUNCTION(name + "#" + i, f_params, returnType));
                        // Establish connection
                        freeEnsures.add(EQ(INVOKE(name + "#" + i,f_args),f_rets.get(i)));
                    }
                }
            }
        }
        // Construct procedure prototype
        decls.add(new Decl.Procedure(name, params, returns, requires, ensures, freeRequires, freeEnsures, Collections.EMPTY_LIST, modifies, null));
        //
        return decls;
    }

    public List<Decl> constructProcedureImplementation(WyilFile.Decl.FunctionOrMethod d, String name, List<Decl.Parameter> params, List<Decl.Parameter> returns, List<Expr.Logical> requires, List<Expr.Logical> ensures, Stmt body) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Add useful heading
        decls.addAll(constructCommentSubheading("Implementation"));
        // Construct (shadow) parameters
        List<Decl.Parameter> shadows = map(params, p -> new Decl.Parameter(p.getName() + "#", p.getType()));
        // Determine local variables
        List<Decl.Variable> locals = constructLocals(d.getBody());
        // Add shadow declarations and assignments to the body
        List<Stmt> stmts = constructShadowAssignments(params, locals);
        // Add actual body
        stmts.add(body);
        // Check whether last statement is a return or not.
        if (!hasFinalReturn(d)) {
            // Return the updated program heap (only for methods).
            stmts.add(RETURN(ATTRIBUTE(d)));
        }
        // Construct implementation which can be checked against its specification.
        decls.add(new Decl.Implementation(name, shadows, returns, locals, SEQUENCE(stmts)));
        // Add the "lambda" value
        decls.add(new Decl.Constant(true, name + "#lambda", LAMBDA));
        //
        return decls;
    }

    private List<Stmt> constructShadowAssignments(List<Decl.Parameter> params, List<Decl.Variable> locals) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        for (int i = 0; i != params.size(); ++i) {
            Decl.Parameter ith = params.get(i);
            // Add local variable declaration for parameter
            locals.add(new Decl.Variable(ith.getName(), ith.getType()));
            // Add assignment from shadow to parameter
            stmts.add(ASSIGN(VAR(ith.getName()),VAR(ith.getName() + "#")));
        }
        return stmts;
    }

    private List<Decl> constructLambdaAxioms(WyilFile.Decl.Function d, WyilFile.Type.Callable instantiation) {
        WyilFile.Type param = d.getType().getParameter();
        WyilFile.Type ret = d.getType().getReturn();
        String name = toMangledName(d, instantiation) + "#lambda";
        return constructLambdaAxioms(name, param, ret, d.getTemplate(), d);
    }

    private List<Decl> constructLambdaAxioms(String name, WyilFile.Type param, WyilFile.Type ret, Tuple<WyilFile.Template.Variable> template, SyntacticItem item) {
        // Construct template parameters
        ArrayList<Decl.Parameter> params = new ArrayList<>();
        params.add(HEAP_PARAM);
        for(int i=0;i!=template.size();++i) {
            params.add(new Decl.Parameter(template.get(i).getName().get(),TYPE));
        }
        final int n = param.shape();
        ArrayList<Decl> decls = new ArrayList<>();
        // Add the lambda value
        decls.add(new Decl.Constant(true, name, LAMBDA));
        // Add axiom(s) for the return values
        Expr[] axioms = new Expr[ret.shape()];
        for (int i = 0; i != axioms.length; ++i) {
            Expr.Logical axiom = constructTypeTest(ret.dimension(i), WyilFile.Type.Any, INVOKE("Lambda#return", VAR(name), CONST(i)), HEAP, item);
            if(params.size() > 0) {
                axiom = FORALL(params,axiom);
            }
            decls.add(new Decl.Axiom(axiom));
        }
        return decls;
    }

    /**
     * Convert a sequence of Wyil parameter declarations into a sequence of Boogie parameter declarations. This requires
     * converting the Wyil type to its corresponding Boogie type.
     *
     * @param template     Whiley template parameters to include (if applicable)
     * @param parameters.  Whiley parameter / return declarations for conversion.
     * @param constraints. Any constraints generated from parameter types will be added to this list of constraints.
     * @param heap.        Identifies the correct name to use when referring to the heap. This matters as in some
     *                     contexts one must refer to the new heap, and in others to the "old" heap.
     * @param shadow.      Indicates whether or not to generate "shadow" parameter names.
     * @return
     */
    public Pair<List<Decl.Parameter>, List<Expr.Logical>> constructParameters(WyilFile.Tuple<WyilFile.Template.Variable> template, WyilFile.Tuple<WyilFile.Decl.Variable> parameters, Expr heap) {
        ArrayList<Decl.Parameter> params = new ArrayList<>();
        ArrayList<Expr.Logical> constraints = new ArrayList<>();
        // add template (if applicable)
        if(template != null) {
            // Add template parameters (if applicable)
            for (int i = 0; i != template.size(); ++i) {
                WyilFile.Template.Variable ith = template.get(i);
                params.add(new Decl.Parameter(ith.getName().get(), TYPE));
            }
        }
        // Add actual parameters
        for (int i = 0; i != parameters.size(); ++i) {
            WyilFile.Decl.Variable ith = parameters.get(i);
            String name = toVariableName(ith);
            params.add(new Decl.Parameter(name, constructType(ith.getType())));
            // Construct any constraints arising from the parameter's type
            Expr.Logical constraint = constructTypeConstraint(ith.getType(), VAR(name), heap, ith);
            //
            if (constraint != null) {
                constraints.add(constraint);
            }
        }
        return new Pair<>(params, constraints);
    }

    /**
     * Construct a set of parameters which have no explictly declared name in the original Whiley source file. This
     * situation arises for lambda's primarily.
     *
     * @param prefix      Prefix to use for variable names.
     * @param types       Types of anonymous parameters.
     * @param constraints Any constraints generated from parameter types will be added to this list of constraints.
     * @param heap        Identifies the correct name to use when referring to the heap. This matters as in some
     *                    contexts one must refer to the new heap, and in others to the "old" heap.
     * @return
     */
    public Pair<List<Decl.Parameter>, List<Expr.Logical>> constructAnonymousParameters(String prefix, WyilFile.Type type, Expr heap) {
        ArrayList<Decl.Parameter> parameters = new ArrayList<>();
        ArrayList<Expr.Logical> constraints = new ArrayList<>();
        //
        for (int i = 0; i != type.shape(); ++i) {
            String name = prefix + "#" + i;
            parameters.add(new Decl.Parameter(name, constructType(type.dimension(i))));
            // Construct any constraints arising from the parameter's type
            Expr.Logical constraint = constructTypeConstraint(type.dimension(i), VAR(name), heap, type);
            //
            if (constraint != null) {
                constraints.add(constraint);
            }
        }
        return new Pair<>(parameters, constraints);
    }

    /**
     * Determine the set of local variables declared within this block. This is necessary as Boogie, unlike Whiley,
     * requires that all local variables are declared up front (like C does).
     *
     * @param blk
     * @return
     */
    public List<Decl.Variable> constructLocals(WyilFile.Stmt blk) {
        ArrayList<Decl.Variable> decls = new ArrayList<>();
        // Handle local variables
        new AbstractVisitor(meter) {
            @Override
            public void visitLambda(WyilFile.Decl.Lambda decl) {
                // NOTE: we don't construct locals through a lambda since the body of the lambda
                // will be extracted into a standalone procedure.
            }

            @Override
            public void visitInitialiser(WyilFile.Stmt.Initialiser stmt) {
                super.visitInitialiser(stmt);
                WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
                for (int i = 0; i != vars.size(); ++i) {
                    WyilFile.Decl.Variable ith = vars.get(i);
                    String name = toVariableName(ith);
                    decls.add(new Decl.Variable(name, constructType(ith.getType())));
                }
            }

            @Override
            public void visitAssign(WyilFile.Stmt.Assign stmt) {
                super.visitAssign(stmt);
                if (!WyilUtils.isSimple(stmt) && WyilUtils.hasInterference(stmt, meter)) {
                    Tuple<WyilFile.LVal> lhs = stmt.getLeftHandSide();
                    for (int i = 0, k = 0; i != lhs.size(); ++i) {
                        WyilFile.LVal lv = lhs.get(i);
                        WyilFile.Type t = lv.getType();
                        for (int j = 0; j != t.shape(); ++j) {
                            Type type = constructType(t.dimension(j));
                            decls.add(new Decl.Variable(TEMP(stmt, k), type));
                            k = k + 1;
                        }
                    }
                }
            }

            @Override
            public void visitFor(WyilFile.Stmt.For stmt) {
                super.visitFor(stmt);
                WyilFile.Decl.StaticVariable v = stmt.getVariable();
                String name = toVariableName(v);
                Type type = constructType(v.getType());
                decls.add(new Decl.Variable(name, type));
                //
                if(!isPure(stmt)) {
                    // Loop modifies heap in some way.  Hence, need to store a copy of HEAP at beginning of loop which
                    // can be used as the reference point.
                    decls.add(new Decl.Variable("HEAP$" + stmt.getIndex(), REFMAP));
                }
            }

            @Override
            public void visitWhile(WyilFile.Stmt.While stmt) {
                super.visitWhile(stmt);
                if(!isPure(stmt)) {
                    // Loop modifies heap in some way.  Hence, need to store a copy of HEAP at beginning of loop which
                    // can be used as the reference point.
                    decls.add(new Decl.Variable("HEAP$" + stmt.getIndex(), REFMAP));
                }
            }

            @Override
            public void visitDoWhile(WyilFile.Stmt.DoWhile stmt) {
                super.visitDoWhile(stmt);
                if(!isPure(stmt)) {
                    // Loop modifies heap in some way.  Hence, need to store a copy of HEAP at beginning of loop which
                    // can be used as the reference point.
                    decls.add(new Decl.Variable("HEAP$" + stmt.getIndex(), REFMAP));
                }
            }

            @Override
            public void visitDeclaration(WyilFile.Decl d) {
                // Prevent unexpected traverals of declarations.
            }

            @Override
            public void visitNew(WyilFile.Expr.New expr) {
                super.visitNew(expr);
                String name = TEMP(expr);
                decls.add(new Decl.Variable(name, REF));
            }

            @Override
            public void visitInvoke(WyilFile.Expr.Invoke expr) {
                super.visitInvoke(expr);
                WyilFile.Decl.Callable ft = expr.getLink().getTarget();
                if (ft instanceof WyilFile.Decl.FunctionOrMethod) {
                    WyilFile.Type type = ft.getType().getReturn();
                    if (type.shape() == 1) {
                        // Construct temporary variable
                        decls.add(new Decl.Variable(TEMP(expr), constructType(type)));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            decls.add(new Decl.Variable(TEMP(expr, i),
                                    constructType(type.dimension(i))));
                        }
                    }
                }
            }

            @Override
            public void visitIndirectInvoke(WyilFile.Expr.IndirectInvoke expr) {
                super.visitIndirectInvoke(expr);
                WyilFile.Type.Callable ft = expr.getSource().getType().as(WyilFile.Type.Callable.class);
                //
                if (!(ft instanceof WyilFile.Type.Property)) {
                    WyilFile.Type type = expr.getType();
                    if (type.shape() == 1) {
                        // Construct temporary variable
                        decls.add(new Decl.Variable(TEMP(expr), constructType(ft.getReturn())));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            Type ith = constructType(ft.getReturn().dimension(i));
                            decls.add(new Decl.Variable(TEMP(expr, i),
                                    constructType(type.dimension(i))));
                        }
                    }
                }
            }

            @Override
            public void visitType(WyilFile.Type t) {
                // Prevent unexpected traverals of types
            }
        }.visitStatement(blk);
        // Done
        return decls;
    }

    /**
     * Construct any lambda's which are used within a given declaration (e.g. for a function). These are translated as
     * separate functions. For example, consider this Whiely code:
     *
     * <pre>
     * method test():
     *    fun_t fn = &(int x -> x+1)
     * </pre>
     * <p>
     * Then, the translation corresponds roughly as though we had written in like so:
     *
     * <pre>
     * method test():
     *    fun_t fn = &l255
     *
     * function l255(int x) -> int:
     *    return x+1
     * </pre>
     *
     * @param d
     * @return
     */
    public List<Decl> constructLambdas(WyilFile.Decl d) {
        ArrayList<Decl> decls = new ArrayList<>();
        List<WyilFile.Decl.Lambda> lambdas = extractLambdaDeclarations(d);
        //
        if (lambdas.size() > 0) {
            decls.add(new Decl.LineComment("// Anon lambdas"));
        }
        //
        for (int i = 0; i != lambdas.size(); ++i) {
            decls.addAll(constructStandaloneLambda(lambdas.get(i)));
        }
        //
        return decls;
    }

    private List<Decl> constructStandaloneLambda(WyilFile.Decl.Lambda l) {
        // Identify enclosing function/method to figure out names of returns.
        WyilFile.Decl.Callable enclosing = l.getAncestor(WyilFile.Decl.FunctionOrMethod.class);
        //
        WyilFile.Type.Callable type = l.getType();
        WyilFile.Type returnType = type.getReturn();
        boolean method = (type instanceof WyilFile.Type.Method);
        // Determine any unbound type variables (if applicable)
        Tuple<WyilFile.Template.Variable> template = enclosing != null ? enclosing.getTemplate() : new Tuple<>();
        // Extract variables captured in the lambda
        Set<WyilFile.Decl.Variable> captured = l.getCapturedVariables(meter);
        //
        String name = "lambda#" + l.getIndex();
        ArrayList<Decl> decls = new ArrayList<>();
        // Convert explicit parameters
        Pair<List<Decl.Parameter>, List<Expr.Logical>> declaredParametersAndConstraints = constructParameters(template, l.getParameters(), HEAP);
        Pair<List<Decl.Parameter>, List<Expr.Logical>> capturedParametersAndConstraints = constructParameters(null, new Tuple<>(l.getCapturedVariables(meter)), HEAP);
        Pair<List<Decl.Parameter>,List<Expr.Logical>> returnsAndConstraints = constructAnonymousParameters("r", returnType, HEAP);
        // Parameters and returns
        List<Decl.Parameter> parameters = append(declaredParametersAndConstraints.first(),capturedParametersAndConstraints.first());
        List<Decl.Parameter> returns = returnsAndConstraints.first();
        // Requires (and ensures?)
        List<Expr.Logical> requires = append(declaredParametersAndConstraints.second(),capturedParametersAndConstraints.second());
        List<Expr.Logical> ensures = returnsAndConstraints.second();
        // Add lambda implementation
        decls.add(constructStandaloneLambdaPrototype(l, name, parameters, returns, requires, ensures));
        decls.add(constructStandaloneLambdaImplementation(l, name, parameters, returns));
        // Add the "lambda" value
        decls.addAll(constructLambdaAxioms(name, type.getParameter(), returnType, template, l));
        // Done
        return decls;
    }

    private Decl constructStandaloneLambdaPrototype(WyilFile.Decl.Lambda l, String name, List<Decl.Parameter> params, List<Decl.Parameter> returns, List<Expr.Logical> requires, List<Expr.Logical> ensures) {
        WyilFile.Type.Callable type = l.getType();
        boolean method = (type instanceof WyilFile.Type.Method);
        // Add Context Level Guarantee
        requires.add(GT(VAR("Context#Level"), CONST(1)));
        // Method's modify the heap
        List<String> modifies = method ? Arrays.asList("HEAP") : Collections.EMPTY_LIST;
        // Add lambda implementation
        return new Decl.Procedure(name, params, returns, requires, ensures,
                modifies);
    }

    private Decl constructStandaloneLambdaImplementation(WyilFile.Decl.Lambda l, String name, List<Decl.Parameter> params, List<Decl.Parameter> returns) {
        WyilFile.Type.Callable type = l.getType();
        WyilFile.Type returnType = type.getReturn();
        boolean method = (type instanceof WyilFile.Type.Method);
        // Construct (shadow) parameters
        List<Decl.Parameter> shadows = map(params, p -> new Decl.Parameter(p.getName() + "#", p.getType()));
        // Extract any necessary local variable declarations
        List<Decl.Variable> locals = constructLocals(l.getBody());
        // Add shadow declarations and assignments to the body
        List<Stmt> stmts = constructShadowAssignments(params,locals);
        // Translate lambda body
        Expr body = visitExpression(l.getBody());
        // Add all preconditions arising. If there are any, they will likely fail!
        Pair<List<Stmt>,List<Expr>> f = flatternImpureExpressions(body);
        stmts.addAll(f.first());
        // Add return variable assignments
        List<Expr> tuple = f.second();
        for(int i=0;i!=returnType.shape();++i) {
            stmts.add(ASSIGN(VAR("r#" + i), tuple.get(i)));
        }
        return new Decl.Implementation(name, shadows, returns, locals, SEQUENCE(stmts));
    }

    @Override
    public Expr constructLambda(WyilFile.Decl.Lambda decl, Expr body) {
        // Read out its "lambda" value
        return VAR("lambda#" + decl.getIndex());
    }

    @Override
    public Stmt constructAssert(WyilFile.Stmt.Assert stmt, Expr condition) {
        // Flattern (potentially impure) condition
        Pair<List<Stmt>, Expr> f = flatternImpureExpression(condition);
        // Add side effects
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        // Add assertion itself, along with relevant attributes for disambiguation
        stmts.add(ASSERT((Expr.Logical) f.second(), ATTRIBUTE(stmt.getCondition()), ATTRIBUTE(WyilFile.STATIC_ASSERTION_FAILURE)));
        // DONE
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructAssign(WyilFile.Stmt.Assign stmt, List _lhs, List _rhs) {
        List<WyilFile.LVal> lvals = flatternLVals(stmt.getLeftHandSide());
        List<WyilFile.Expr> rvals = flatternRVals(stmt.getRightHandSide());
        // Flattern left-hand side
        Pair<List<Stmt>,List<Expr>> fl = flatternImpureExpressions(_lhs);
        ArrayList<Stmt> stmts = new ArrayList<>(fl.first());
        List<Expr> lhs = fl.second();
        // Flattern right-hand side
        Pair<List<Stmt>,List<Expr>> fr = flatternImpureExpressions(_rhs);
        stmts.addAll(fr.first());
        List<Expr> rhs = fr.second();
        // Third, coerce right-hand side elements
        rhs = coerceAssignmentRightHandSide(lvals, stmt.getRightHandSide(), rhs);
        // Fourth, determine whether simple assign sufficient (or not)
        if (!WyilUtils.isSimple(stmt) && WyilUtils.hasInterference(stmt, meter)) {
            // Simple assignment is insufficient. Therefore, we need to assign every element
            // on the right-hand side into a temporary variable before (subsequently)
            // assigning it into the corresponding item on the left-hand side.
            for (int i = 0; i != rhs.size(); ++i) {
                // Assign item on rhs into temporary
                stmts.add(ASSIGN(VAR(TEMP(stmt, i)), rhs.get(i)));
                // Setup assignment from temporary to the lhs
                rhs.set(i, VAR(TEMP(stmt, i)));
            }
        }
        // Next, action assignments
        for (int i = 0; i != lvals.size(); ++i) {
            stmts.add(constructAssign(lvals.get(i), lhs.get(i), rhs.get(i)));
        }
        // Finally, action type tests
        for (int i = 0; i != lvals.size(); ++i) {
            WyilFile.LVal ith = lvals.get(i);
            // Extract the assigned variable
            WyilFile.Decl.Variable v = extractVariable(ith, meter);
            // Apply type constraint (if applicable)
            Expr.Logical c = constructTypeConstraint(v.getType(), VAR(toVariableName(v)), HEAP, ith);
            if (c != null) {
                stmts.add(ASSERT(c, ATTRIBUTE(rvals.get(i)), ATTRIBUTE(WyilFile.STATIC_TYPEINVARIANT_FAILURE)));
            }
        }
        // Done
        return SEQUENCE(stmts);
    }

    /**
     * Flatten the left-hand side into an array of individual lvals. For example:
     *
     * <pre>
     * x,(y,z) = 1,f()
     * </pre>
     * <p>
     * The left-hand side of the assignment would be flatterned into
     * <code>x,y,z</code>. The purpose of flattening is simply to align primitive
     * assignments on the left-hand side with those on the right hand side. In a general sense, this doesn't work
     * because (as above) we may have fewer items on the right-hand side (strictly speaking). However, in this Boogie
     * translation this will never arise because <code>FauxTuple</code>s have been employed to ensure they line up. More
     * specifically, the above would become:
     *
     * <pre>
     * x,y,z = 1,f#1(),f#2
     * </pre>
     *
     * @param lhs
     * @return
     */
    private List<WyilFile.LVal> flatternLVals(Tuple<WyilFile.LVal> lhs) {
        ArrayList<WyilFile.LVal> lvals = new ArrayList<>();
        for (int i = 0; i != lhs.size(); ++i) {
            WyilFile.LVal ith = lhs.get(i);
            if (ith instanceof WyilFile.Expr.TupleInitialiser) {
                Tuple<WyilFile.Expr> ti = ((WyilFile.Expr.TupleInitialiser) ith).getOperands();
                for (int j = 0; j < ti.size(); ++j) {
                    lvals.add((WyilFile.LVal) ti.get(j));
                }
            } else {
                lvals.add(ith);
            }
        }
        return lvals;
    }

    private List<WyilFile.Expr> flatternRVals(Tuple<WyilFile.Expr> rhs) {
        ArrayList<WyilFile.Expr> rvals = new ArrayList<>();
        // First, flattern all rvals
        for (int i = 0; i != rhs.size(); ++i) {
            WyilFile.Expr ith = rhs.get(i);
            int n = ith.getType().shape();
            if(n > 1) {
                if (ith instanceof WyilFile.Expr.TupleInitialiser) {
                    WyilFile.Expr.TupleInitialiser ti = (WyilFile.Expr.TupleInitialiser) ith;
                    rvals.addAll(flatternRVals(ti.getOperands()));
                } else {
                    // This may seem a bit weird, but it's the best we can do in the circumstance
                    for(int j=0;j<n;++j) {
                        rvals.add(ith);
                    }
                }
            } else {
                rvals.add(ith);
            }
        }
        return rvals;
    }

    /**
     * Coerce elements on the right-hand side of an assignment. This is necessary because some types in Boogie are boxed
     * (e.g. arrays or unions), where as others are not (e.g. ints or booleans). Thus, consider the following:
     *
     * <pre>
     * int|null x = ...
     * ...
     * x = 1
     * </pre>
     * <p>
     * In this case, the right-hand side has primitive (Boogie) type
     * <code>int</code> (which is not boxex). whilst the left-hand side has (Boogie)
     * type <code>Value</code> (which is boxed). Therefore, we need to box the right-hand side prior to the assignment.
     *
     * @param lvals
     * @param rhs
     * @param rvals
     * @return
     */
    private List<Expr> coerceAssignmentRightHandSide(List<WyilFile.LVal> lvals, Tuple<WyilFile.Expr> rhs, List<Expr> rvals) {
        for (int i = 0, k = 0; i != rhs.size(); ++i) {
            WyilFile.Type t = rhs.get(i).getType();
            for (int j = 0; j < t.shape(); ++j) {
                WyilFile.Type l = lvals.get(k).getType();
                WyilFile.Type r = t.dimension(j);
                rvals.set(k, cast(l, r, rvals.get(k)));
                k = k + 1;
            }
        }
        return rvals;
    }

    /**
     * Construct an assignment statement for a given lhs and rhs. The challenge here stems from the requirement in
     * Boogie that we cannot assign to multiple nested dictionaries (e.g. <code>xs[i][j] = ...</code> is not
     * permitted).
     *
     * @param lval Raw left-hand side
     * @param rhs  Translated and coerced right-hand side(s)
     * @return
     */
    private Stmt constructAssign(WyilFile.LVal lval, Expr lhs, Expr rhs) {
        switch (lval.getOpcode()) {
            case WyilFile.EXPR_arrayaccess:
            case WyilFile.EXPR_arrayborrow: {
                Expr.DictionaryAccess l = (Expr.DictionaryAccess) lhs;
                WyilFile.Expr.ArrayAccess v = (WyilFile.Expr.ArrayAccess) lval;
                // Reconstruct source as expression
                Expr src = visitExpression(v.getFirstOperand());
                // Flattern reconstructed source
                src = flatternImpureExpression(src).second();
                // Box right-hand side (as necessary)
                rhs = PUT(src, l.getIndex(), box(lval.getType(), rhs));
                // Recurse assignment
                return constructAssign((WyilFile.LVal) v.getFirstOperand(), l.getSource(), rhs);
            }
            case WyilFile.EXPR_recordaccess:
            case WyilFile.EXPR_recordborrow: {
                Expr.DictionaryAccess l = (Expr.DictionaryAccess) lhs;
                WyilFile.Expr.RecordAccess v = (WyilFile.Expr.RecordAccess) lval;
                // Reconstruct source as expression
                Expr src = visitExpression(v.getOperand());
                // Flattern reconstructed source
                src = flatternImpureExpression(src).second();
                // Box right-hand side (as necessary)
                rhs = PUT(src, l.getIndex(), box(lval.getType(), rhs));
                // Recurse assignment
                return constructAssign((WyilFile.LVal) v.getOperand(), l.getSource(), rhs);
            }
            case WyilFile.EXPR_dereference: {
                Expr.DictionaryAccess l = (Expr.DictionaryAccess) lhs;
                WyilFile.Expr.Dereference v = (WyilFile.Expr.Dereference) lval;
                // Reconstruct source as expression
                Expr src = visitExpression(v.getOperand());
                // Flattern reconstructed source
                src = flatternImpureExpression(src).second();
                // Box right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                // Construct assignment
                return ASSIGN(HEAP, PUT(HEAP, src, rhs));
            }
            case WyilFile.EXPR_fielddereference: {
                Expr.DictionaryAccess r = (Expr.DictionaryAccess) lhs;
                Expr.DictionaryAccess h = (Expr.DictionaryAccess) r.getSource();
                WyilFile.Expr.FieldDereference fr = (WyilFile.Expr.FieldDereference) lval;
                // Extract the source reference type
                WyilFile.Type.Reference refT = fr.getOperand().getType().as(WyilFile.Type.Reference.class);
                // Extract the source record type
                WyilFile.Type.Record recT = refT.getElement().as(WyilFile.Type.Record.class);
                // Reconstruct source as expression
                Expr src = visitExpression(fr.getOperand());
                // Flattern reconstructed source
                src = flatternImpureExpression(src).second();
                // Reconstruct index expression
                Expr index = VAR("$" + fr.getField());
                // Box the right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                // Make the field assignment
                rhs = PUT(unbox(recT, GET(HEAP, src)), index, rhs);
                // Box again!
                rhs = box(recT, rhs);
                // Construct assignment
                return ASSIGN(HEAP, PUT(HEAP, src, rhs));
            }
            case WyilFile.EXPR_variablecopy:
            case WyilFile.EXPR_variablemove: {
                WyilFile.Expr.VariableAccess expr = (WyilFile.Expr.VariableAccess) lval;
                WyilFile.Decl.Variable decl = expr.getVariableDeclaration();
                String name = toVariableName(expr.getVariableDeclaration());
                // NOTE: the manner in which the following cast is applied seems odd to me, and is an artifact of how WyC is currently typing assignments.
                return ASSIGN(VAR(name), cast(decl.getType(), expr.getType(), rhs));
            }
            default:
                throw new UnsupportedOperationException("invalid lval");
        }
    }

    @Override
    public Stmt constructAssume(WyilFile.Stmt.Assume stmt, Expr condition) {
        // Flattern (potentially impure) condition
        Pair<List<Stmt>, Expr> f = flatternImpureExpression(condition);
        // Add side effects
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        //
        stmts.add(ASSUME((Expr.Logical) f.second(), ATTRIBUTE(stmt.getCondition()), ATTRIBUTE(WyilFile.STATIC_ASSUMPTION_FAILURE)));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructBlock(WyilFile.Stmt.Block stmt, List<Stmt> stmts) {
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructBreak(WyilFile.Stmt.Break stmt) {
        WyilFile.Stmt loop = getEnclosingLoop(stmt);
        return GOTO("BREAK_" + loop.getIndex());
    }

    @Override
    public Stmt constructContinue(WyilFile.Stmt.Continue stmt) {
        WyilFile.Stmt loop = getEnclosingLoop(stmt);
        return GOTO("CONTINUE_" + loop.getIndex());
    }

    @Override
    public Stmt constructDebug(WyilFile.Stmt.Debug stmt, Expr operand) {
        // Flattern (potentially impure) expression
        Pair<List<Stmt>,Expr> f = flatternImpureExpression(operand);
        // Add all side-effects and assertions
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        //
        stmts.add(ASSERT(CONST(true)));
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructDoWhile(WyilFile.Stmt.DoWhile stmt, Stmt body, Expr condition, List invariant) {
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        boolean pure = isPure(stmt);
        Expr.VariableAccess OHEAP = BoogieFile.VAR("HEAP$" + stmt.getIndex());
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add first iteration
        stmts.add(body);
        // Flattern (potentiall impure) condition
        Pair<List<Stmt>,Expr> f = flatternImpureExpression(condition);
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(LABEL("CONTINUE_" + stmt.getIndex()));
        }
        // Add all side effects & checks
        stmts.addAll(f.first());
        body = SEQUENCE(append(body, f.first()));
        // Preprepend the necessary definedness checks
        invariant = flatternAsLogical(invariant);
        // Add type constraints arising from modified variables
        invariant.addAll(0, constructTypeConstraints(modified, HEAP));
        if(!pure) {
            // Save OLD heap
            stmts.add(BoogieFile.ASSIGN(OHEAP,HEAP));
            // Add necessary loop frame
            invariant.addAll(constructLoopFrame(stmt,OHEAP,HEAP));
        }
        // Add the loop itself
        stmts.add(WHILE((Expr.Logical) f.second(), invariant, body));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(LABEL("BREAK_" + stmt.getIndex()));
        }
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructFail(WyilFile.Stmt.Fail stmt) {
        return ASSERT(CONST(false, ATTRIBUTE(stmt)), ATTRIBUTE(WyilFile.STATIC_FAULT));
    }

    @Override
    public Stmt constructFor(WyilFile.Stmt.For stmt, Pair<Expr,Expr> range, List<Expr> _invariant, Stmt body) {
        List<Expr.Logical> invariant = flatternAsLogical(_invariant);
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        boolean pure = isPure(stmt);
        Expr.VariableAccess OHEAP = BoogieFile.VAR("HEAP$" + stmt.getIndex());
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        // Determine name of loop variable
        String name = toVariableName(stmt.getVariable());
        Expr.VariableAccess var = VAR(name);
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Flattern (potentiall impure) condition
        Pair<List<Stmt>,Expr> lhs = flatternImpureExpression(range.first());
        Pair<List<Stmt>,Expr> rhs = flatternImpureExpression(range.second());
        // Add all assertions and side effects
        stmts.addAll(lhs.first());
        stmts.addAll(rhs.first());
        // Extract loop contents so it can be appended later
        ArrayList<Stmt> loopBody = new ArrayList<>();
        loopBody.add(body);
        // Initialise index variable with first value from range
        stmts.add(ASSIGN(var, lhs.second()));
        Expr condition = LT(var, rhs.second());
        // Add variable increment for completeness
        loopBody.add(ASSIGN(var, ADD(var, CONST(1))));
        // Update invariant
        invariant.add(0, AND(LTEQ(lhs.second(), var), LTEQ(var, rhs.second()),ATTRIBUTE(stmt.getVariable().getInitialiser())));
        // Preprepend the necessary definedness checks
        invariant = flatternAsLogical(invariant);
        // Add any type constraints arising
        invariant.addAll(0, constructTypeConstraints(modified, HEAP));
        if(!pure) {
            // Save OLD heap
            stmts.add(BoogieFile.ASSIGN(OHEAP,HEAP));
            // Add necessary loop frame
            invariant.addAll(constructLoopFrame(stmt,OHEAP,HEAP));
        }
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(LABEL("CONTINUE_" + stmt.getIndex()));
        }
        // Construct the loop
        stmts.add(WHILE((Expr.Logical) condition, invariant, SEQUENCE(loopBody)));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(LABEL("BREAK_" + stmt.getIndex()));
        }
        // Done.
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructIfElse(WyilFile.Stmt.IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch) {
        // Flattern (potentially impure) condition
        Pair<List<Stmt>, Expr> f = flatternImpureExpression(condition);
        // Add side effects
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        // Add statement!
        stmts.add(IFELSE((Expr.Logical) f.second(), trueBranch, falseBranch));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructInitialiser(WyilFile.Stmt.Initialiser stmt, Expr init) {
        WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
        //
        if (init == null) {
            return SEQUENCE();
        } else {
            // Flattern (potentially impure) expression
            Pair<List<Stmt>, List<Expr>> f = flatternImpureExpressions(init);
            // Add all preconditions arising.
            ArrayList<Stmt> stmts = new ArrayList<>(f.first());
            // Extract list of initialiser expressions
            List<Expr> inits = f.second();
            // Determine type of initialiser expression
            WyilFile.Type initT = stmt.getInitialiser().getType();
            // Assign to each variable and check constraints
            for (int i = 0; i != vars.size(); ++i) {
                WyilFile.Decl.Variable ith = vars.get(i);
                String name = toVariableName(ith);
                stmts.add(ASSIGN(VAR(name), cast(ith.getType(), initT.dimension(i), inits.get(i))));
                // Add assertion for type constraints (if applicable)
                Expr.Logical c = constructTypeConstraint(ith.getType(), VAR(name), HEAP, ith);
                if (c != null) {
                    stmts.add(ASSERT(c, ATTRIBUTE(stmt.getInitialiser()), ATTRIBUTE(WyilFile.STATIC_TYPEINVARIANT_FAILURE)));
                }
            }
            // FIXME: need post condition!
            return SEQUENCE(stmts);
        }
    }

    @Override
    public Stmt constructInvokeStmt(WyilFile.Expr.Invoke expr, List<Expr> _args) {
        WyilFile.Type.Callable ft = expr.getLink().getTarget().getType();
        // Flattern (potentially impure) arguments
        Pair<List<Stmt>, List<Expr>> f = flatternImpureExpressions(_args);
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        List<Expr> args = f.second();
        //
        if (ft instanceof WyilFile.Type.Property) {
            // NOTE: this case arises when for a property invocation which discards the
            // return value. That doesn't really make sense, and for now we just treat as a
            // "skip".
            stmts.add(ASSERT(CONST(true)));
        } else {
            WyilFile.Type.Callable mt = (WyilFile.Type.Callable) ft;
            // Extract template arguments
            Tuple<WyilFile.Type> binding = expr.getBinding().getArguments();
            // Extract declared return type
            WyilFile.Type type = mt.getReturn();
            // Apply name mangling
            String name = toMangledName(expr.getLink().getTarget());
            // Determine lvals. Observe that we have to assign any return values from the
            // procedure called, even if they are never used.
            List<LVal> lvals = new ArrayList<>();
            if (type.shape() == 1) {
                lvals.add(VAR(TEMP(expr)));
            } else {
                for (int i = 0; i != type.shape(); ++i) {
                    lvals.add(VAR(TEMP(expr, i)));
                }
            }
            // Apply conversions to arguments as necessary
            args = cast(mt.getParameter(), expr.getOperands(), args);
            // Add template arguments
            for(int i=0;i!=binding.size();++i) {
                args.add(i,constructMetaType(binding.get(i), HEAP));
            }
            // Done
            stmts.add(CALL(name, lvals, args, ATTRIBUTE(expr)));
        }
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructIndirectInvokeStmt(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> args) {
        WyilFile.Type.Callable ft = expr.getSource().getType().as(WyilFile.Type.Callable.class);
        // Flattern (potentially impure) expressions
        Pair<List<Stmt>, Expr> f1 = flatternImpureExpression(source);
        Pair<List<Stmt>, List<Expr>> f2 = flatternImpureExpressions(args);
        // Add side effects
        ArrayList<Stmt> stmts = new ArrayList<>(f1.first());
        stmts.addAll(f2.first());
        //
        args = f2.second();
        //
        if (ft instanceof WyilFile.Type.Property) {
            // NOTE: this case arises when for a property invocation which discards the
            // return value. That doesn't really make sense, and for now we just treat as a
            // "skip".
            stmts.add(ASSERT(CONST(true)));
        } else {
            // Extract declared return type
            WyilFile.Type type = ft.getReturn();
            // Extract any holes
            Tuple<WyilFile.Template.Variable> holes = WyilUtils.extractTemplate(ft,meter);
            // Determine lvals. Observe that we have to assign any return values from the
            // procedure called, even if they are never used.
            List<LVal> lvals = new ArrayList<>();
            if (type.shape() == 1) {
                lvals.add(VAR("m#" + expr.getIndex()));
            } else {
                for (int i = 0; i != type.shape(); ++i) {
                    lvals.add(VAR("m#" + expr.getIndex() + "#" + i));
                }
            }
            // Add method pointer
            args.add(0, f1.second());
            // Add meta types arguments (if any)
            int i = 2;
            for(WyilFile.Template.Variable hole : holes) {
                args.add(i++,VAR(hole.getName().get()));
            }
            // Determine the methods name
            String name = toLambdaMangle(ft);
            // Done
            stmts.add(CALL(name, lvals, args, ATTRIBUTE(expr)));
        }
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructNamedBlock(WyilFile.Stmt.NamedBlock stmt, List<Stmt> stmts) {
        // Named blocks are really a relic from the past which probably cannot currently
        // be encountered at the source-level in Whiley.
        throw new UnsupportedOperationException();
    }

    @Override
    public Stmt constructReturn(WyilFile.Stmt.Return stmt, Expr ret) {
        // Identify enclosing function/method to figure out names of returns.
        WyilFile.Decl.Callable enclosing = stmt.getAncestor(WyilFile.Decl.FunctionOrMethod.class);
        // Construct return value assignments
        ArrayList<Stmt> stmts = new ArrayList<>();
        //
        if (ret != null) {
            WyilFile.Tuple<WyilFile.Decl.Variable> returns = enclosing.getReturns();
            WyilFile.Type type = stmt.getReturn().getType();
            // Flattern (potentially impure) expression
            Pair<List<Stmt>, List<Expr>> f = flatternImpureExpressions(ret);
            // Add all preconditions / side effects arising.
            stmts.addAll(f.first());
            // Extract return values
            List<Expr> rvs = f.second();
            //
            for (int i = 0; i != rvs.size(); ++i) {
                WyilFile.Decl.Variable ith = returns.get(i);
                String rv = toVariableName(ith);
                // Cast returned value as necessary
                Expr re = cast(ith.getType(), type.dimension(i), rvs.get(i));
                // Done
                stmts.add(ASSIGN(VAR(rv), re));
            }
        }
        // Add the actual return statement!
        stmts.add(RETURN(ATTRIBUTE(stmt)));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructSkip(WyilFile.Stmt.Skip stmt) {
        return ASSERT(CONST(true));
    }

    @Override
    public Stmt constructSwitch(WyilFile.Stmt.Switch stmt, Expr condition, List<Pair<List<Expr>, Stmt>> cases) {
        // Flattern (potentially impure) condition
        Pair<List<Stmt>, Expr> f = flatternImpureExpression(condition);
        // Add side effects
        ArrayList<Stmt> stmts = new ArrayList<>(f.first());
        //
        String breakLabel = "SWITCH_" + stmt.getIndex() + "_BREAK";
        String defaultLabel = "SWITCH_" + stmt.getIndex() + "_DEFAULT";
        Stmt defaultCase = null;
        // Construct case labels (ignoring default)
        List<String> labels = new ArrayList<>();
        for (int i = 0; i != cases.size(); ++i) {
            boolean isDefault = cases.get(i).first().isEmpty();
            if (!isDefault) {
                labels.add("SWITCH_" + stmt.getIndex() + "_" + i);
            }
        }
        // Add branch to default label
        labels.add(defaultLabel);
        // Construct non-deterministic goto
        stmts.add(GOTO(labels));
        // Construct cases
        ArrayList<Expr.Logical> defaultCases = new ArrayList<>();
        for (int i = 0; i != cases.size(); ++i) {
            Pair<List<Expr>, Stmt> ith = cases.get(i);
            List<Expr> ith_first = ith.first();
            ArrayList<Expr.Logical> cs = new ArrayList<>();
            for (int j = 0; j != ith_first.size(); ++j) {
                cs.add(EQ(f.second(), ith_first.get(j)));
                defaultCases.add(NEQ(f.second(), ith_first.get(j)));
            }
            if (cs.isEmpty()) {
                defaultCase = ith.second();
            } else {
                stmts.add(LABEL(labels.get(i)));
                stmts.add(ASSUME(OR(cs)));
                stmts.add(ith.second());
                stmts.add(GOTO(breakLabel));
            }
        }
        // Construct default case
        stmts.add(LABEL(defaultLabel));
        stmts.add(ASSUME(AND(defaultCases)));
        if (defaultCase != null) {
            stmts.add(defaultCase);
        }
        stmts.add(GOTO(breakLabel));
        // Add final break label
        stmts.add(LABEL(breakLabel));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructWhile(WyilFile.Stmt.While stmt, Expr condition, List invariant, Stmt body) {
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        boolean pure = isPure(stmt);
        Expr.VariableAccess OHEAP = BoogieFile.VAR("HEAP$" + stmt.getIndex());
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Flattern (potentiall impure) condition
        Pair<List<Stmt>,Expr> f = flatternImpureExpression(condition);
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(LABEL("CONTINUE_" + stmt.getIndex()));
        }
        // Add all side effects & checks
        stmts.addAll(f.first());
        body = SEQUENCE(append(body, f.first()));
        // Preprepend the necessary definedness checks
        invariant = flatternAsLogical(invariant);
        // Add any type constraints arising (first)
        invariant.addAll(0, constructTypeConstraints(modified, HEAP));
        if (!pure) {
            // Save OLD heap
            stmts.add(BoogieFile.ASSIGN(OHEAP, HEAP));
            // Add necessary loop frame
            invariant.addAll(constructLoopFrame(stmt, OHEAP, HEAP));
        }
        //
        stmts.add(WHILE((Expr.Logical) f.second(), invariant, body));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(LABEL("BREAK_" + stmt.getIndex()));
        }
        return SEQUENCE(stmts);
    }

    @Override
    public Expr constructArrayAccessLVal(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
        return GET(source, index, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructDereferenceLVal(WyilFile.Expr.Dereference expr, Expr operand) {
        return GET(HEAP, operand, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructFieldDereferenceLVal(WyilFile.Expr.FieldDereference expr, Expr operand) {
        // First dereference the pointer.
        Expr deref = GET(HEAP, operand, ATTRIBUTE(expr));
        // Second access the given field.
        return GET(deref, VAR("$" + expr.getField()), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructRecordAccessLVal(WyilFile.Expr.RecordAccess expr, Expr source) {
        return GET(source, VAR("$" + expr.getField()), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructTupleInitialiserLVal(WyilFile.Expr.TupleInitialiser expr, List<Expr> operands) {
        // Done
        return new FauxTuple(operands, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructVariableAccessLVal(WyilFile.Expr.VariableAccess expr) {
        // Determine mangled name of this variable
        String name = toVariableName(expr.getVariableDeclaration());
        //
        return VAR(name, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructArrayAccess(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
        return unbox(expr.getType(), GET(source, index, ATTRIBUTE(expr)));
    }

    @Override
    public Expr constructArrayLength(WyilFile.Expr.ArrayLength expr, Expr source) {
        return INVOKE("Array#Length", Arrays.asList(source), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructArrayGenerator(WyilFile.Expr.ArrayGenerator expr, Expr value, Expr length) {
        WyilFile.Type vt = expr.getFirstOperand().getType();
        WyilFile.Type lt = expr.getSecondOperand().getType();
        return INVOKE("Array#Generator", Arrays.asList(box(vt, value), cast(WyilFile.Type.Int, lt, length)), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructArrayInitialiser(WyilFile.Expr.ArrayInitialiser expr, List<Expr> values) {
        WyilFile.Type elementType = expr.getType().as(WyilFile.Type.Array.class).getElement();
        Expr arr = INVOKE("Array#Empty", Arrays.asList(CONST(values.size())), ATTRIBUTE(expr));
        //
        for (int i = 0; i != values.size(); ++i) {
            WyilFile.Type type = expr.getOperands().get(i).getType();
            Expr ith = box(type, values.get(i));
            arr = PUT(arr, CONST(i), ith, ATTRIBUTE(expr));
        }
        //
        return arr;
    }

    @Override
    public Expr constructBitwiseComplement(WyilFile.Expr.BitwiseComplement expr, Expr operand) {
        return INVOKE("Byte#Not", Arrays.asList(operand), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructBitwiseAnd(WyilFile.Expr.BitwiseAnd expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#And", Arrays.asList(e, operands.get(i)), ATTRIBUTE(expr));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseOr(WyilFile.Expr.BitwiseOr expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#Or", Arrays.asList(e, operands.get(i)), ATTRIBUTE(expr));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseXor(WyilFile.Expr.BitwiseXor expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#Xor", Arrays.asList(e, operands.get(i)), ATTRIBUTE(expr));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseShiftLeft(WyilFile.Expr.BitwiseShiftLeft expr, Expr lhs, Expr rhs) {
        Expr cast = INVOKE("Byte#fromInt", Arrays.asList(rhs), ATTRIBUTE(expr));
        return INVOKE("Byte#Shl", Arrays.asList(lhs, cast), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructBitwiseShiftRight(WyilFile.Expr.BitwiseShiftRight expr, Expr lhs, Expr rhs) {
        Expr cast = INVOKE("Byte#fromInt", Arrays.asList(rhs), ATTRIBUTE(expr));
        return INVOKE("Byte#Shr", Arrays.asList(lhs, cast), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructCast(WyilFile.Expr.Cast expr, Expr operand) {
        return cast(expr.getType(), expr.getOperand().getType(), operand);
    }

    @Override
    public Expr constructConstant(WyilFile.Expr.Constant expr) {
        WyilFile.Type type = expr.getType();
        WyilFile.Type source;
        Expr result;
        WyilFile.Value v = expr.getValue();
        switch (v.getOpcode()) {
            case WyilFile.ITEM_null: {
                source = WyilFile.Type.Null;
                result = VAR("Null");
                break;
            }
            case WyilFile.ITEM_bool: {
                boolean b = ((WyilFile.Value.Bool) v).get();
                source = WyilFile.Type.Bool;
                result = CONST(b, ATTRIBUTE(expr));
                break;
            }
            case WyilFile.ITEM_byte: {
                byte b = ((WyilFile.Value.Byte) v).get();
                source = WyilFile.Type.Byte;
                result = CONST(new byte[]{b}, ATTRIBUTE(expr));
                break;
            }
            case WyilFile.ITEM_int: {
                BigInteger i = ((WyilFile.Value.Int) v).get();
                source = WyilFile.Type.Int;
                result = CONST(i, ATTRIBUTE(expr));
                break;
            }
            case WyilFile.ITEM_utf8: {
                byte[] bytes = ((WyilFile.Value.UTF8) v).get();
                result = INVOKE("Array#Empty", Arrays.asList(CONST(bytes.length, ATTRIBUTE(expr))), ATTRIBUTE(expr));
                //
                for (int i = 0; i != bytes.length; ++i) {
                    Expr ith = box(WyilFile.Type.Int, CONST(bytes[i]));
                    result = PUT(result, CONST(i), ith, ATTRIBUTE(expr));
                }
                source = WyilFile.Type.IntArray;
                break;
            }
            default:
                throw new IllegalArgumentException("unknown constant encountered (" + expr.getClass().getName() + ")");
        }
        // Apply a final cast
        return cast(type,source,result);
    }

    @Override
    public Expr constructDereference(WyilFile.Expr.Dereference expr, Expr operand) {
        return unbox(expr.getType(), GET(HEAP, operand, ATTRIBUTE(expr)));
    }

    @Override
    public Expr constructFieldDereference(WyilFile.Expr.FieldDereference expr, Expr operand) {
        Expr field = VAR("$" + expr.getField().get());
        // Extract the source reference type
        WyilFile.Type.Reference refT = expr.getOperand().getType().as(WyilFile.Type.Reference.class);
        // Extract the source record type
        WyilFile.Type.Record recT = refT.getElement().as(WyilFile.Type.Record.class);
        // Reconstruct source expression
        Expr deref = unbox(recT, GET(HEAP, operand, ATTRIBUTE(expr)));
        //
        return unbox(expr.getType(), GET(deref, field, ATTRIBUTE(expr)));
    }

    @Override
    public Expr constructEqual(WyilFile.Expr.Equal expr, Expr lhs, Expr rhs) {
        WyilFile.Type lhsT = expr.getFirstOperand().getType();
        WyilFile.Type rhsT = expr.getSecondOperand().getType();
        boolean boxing = !lhsT.equals(rhsT);
        //
        if (lhs instanceof FauxTuple) {
            List<Expr> ls = ((FauxTuple) lhs).getItems();
            List<Expr> rs = ((FauxTuple) rhs).getItems();
            Expr.Logical result = null;
            for (int i = 0; i != lhsT.shape(); ++i) {
                Expr l = ls.get(i);
                Expr r = rs.get(i);
                l = boxing ? box(lhsT.dimension(i), l) : l;
                r = boxing ? box(rhsT.dimension(i), r) : r;
                result = i == 0 ? EQ(l, r, ATTRIBUTE(expr)) : AND(result, EQ(l, r), ATTRIBUTE(expr));
            }
            // Done
            return result;
        } else if (boxing) {
            return EQ(box(lhsT, lhs), box(rhsT, rhs), ATTRIBUTE(expr));
        } else {
            return EQ(lhs, rhs, ATTRIBUTE(expr));
        }
    }

    @Override
    public Expr constructIntegerLessThan(WyilFile.Expr.IntegerLessThan expr, Expr lhs, Expr rhs) {
        return LT(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerLessThanOrEqual(WyilFile.Expr.IntegerLessThanOrEqual expr, Expr lhs, Expr rhs) {
        return LTEQ(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerGreaterThan(WyilFile.Expr.IntegerGreaterThan expr, Expr lhs, Expr rhs) {
        return GT(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerGreaterThanOrEqual(WyilFile.Expr.IntegerGreaterThanOrEqual expr, Expr lhs, Expr rhs) {
        return GTEQ(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerNegation(WyilFile.Expr.IntegerNegation expr, Expr operand) {
        return NEG(operand, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerAddition(WyilFile.Expr.IntegerAddition expr, Expr lhs, Expr rhs) {
        return ADD(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerSubtraction(WyilFile.Expr.IntegerSubtraction expr, Expr lhs, Expr rhs) {
        return SUB(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerMultiplication(WyilFile.Expr.IntegerMultiplication expr, Expr lhs, Expr rhs) {
        return MUL(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerDivision(WyilFile.Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
        return IDIV(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIntegerRemainder(WyilFile.Expr.IntegerRemainder expr, Expr lhs, Expr rhs) {
        return REM(lhs, rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructIs(WyilFile.Expr.Is expr, Expr operand) {
        return constructTypeTest(expr.getTestType(), expr.getOperand().getType(), operand, HEAP, expr);
    }

    @Override
    public Expr constructLogicalAnd(WyilFile.Expr.LogicalAnd expr, List operands) {
        return AND(operands, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructLogicalImplication(WyilFile.Expr.LogicalImplication expr, Expr lhs, Expr rhs) {
        return IMPLIES((Expr.Logical) lhs, (Expr.Logical) rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructLogicalIff(WyilFile.Expr.LogicalIff expr, Expr lhs, Expr rhs) {
        return IFF((Expr.Logical) lhs, (Expr.Logical) rhs, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructLogicalNot(WyilFile.Expr.LogicalNot expr, Expr operand) {
        return NOT((Expr.Logical) operand, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructLogicalOr(WyilFile.Expr.LogicalOr expr, List operands) {
        return OR(operands, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructExistentialQuantifier(WyilFile.Expr.ExistentialQuantifier expr, List<Pair<Expr, Expr>> ranges,
                                               Expr body) {
        WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
        List<Decl.Parameter> ps = new ArrayList<>();
        List<Expr.Logical> clauses = new ArrayList<>();
        for (int i = 0; i != params.size(); ++i) {
            Pair<Expr, Expr> ith = ranges.get(i);
            String name = toVariableName(params.get(i));
            ps.add(new Decl.Parameter(name, Type.Int));
            clauses.add(LTEQ(ith.first(), VAR(name)));
            clauses.add(LT(VAR(name), ith.second()));
        }
        clauses.add((Expr.Logical) body);
        return EXISTS(ps, AND(clauses), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructUniversalQuantifier(WyilFile.Expr.UniversalQuantifier expr, List<Pair<Expr, Expr>> ranges,
                                             Expr body) {
        WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
        List<Decl.Parameter> ps = new ArrayList<>();
        List<Expr.Logical> clauses = new ArrayList<>();
        for (int i = 0; i != params.size(); ++i) {
            Pair<Expr, Expr> ith = ranges.get(i);
            String name = toVariableName(params.get(i));
            ps.add(new Decl.Parameter(name, Type.Int));
            clauses.add(LTEQ(ith.first(), VAR(name)));
            clauses.add(LT(VAR(name), ith.second()));
        }
        return FORALL(ps, IMPLIES(AND(clauses), (Expr.Logical) body), ATTRIBUTE(expr));
    }

    @Override
    public Expr constructInvoke(WyilFile.Expr.Invoke expr, List<Expr> arguments) {
        ArrayList<Expr> templateArguments = new ArrayList<>();
        Tuple<WyilFile.Type> binding = expr.getBinding().getArguments();
        // Extract (concrete) type signature
        WyilFile.Type.Callable ft = expr.getLink().getTarget().getType();
        WyilFile.Type ftrt = ft.getReturn();
        // Extract (concrete) return type
        WyilFile.Type rt = expr.getBinding().getConcreteType().getReturn();
        // Add template arguments
        for (int i = 0; i != binding.size(); ++i) {
            templateArguments.add(i,constructMetaType(binding.get(i), HEAP));
        }
        // Apply name mangling
        String name = toMangledName(expr.getLink().getTarget());
        // Apply conversions to arguments as necessary
        arguments = cast(ft.getParameter(), expr.getOperands(), arguments);
        // Add template arguments
        arguments.addAll(0, templateArguments);
        // Add heap argument
        arguments.add(0,HEAP);
        //
        if (rt.shape() == 1) {
            return cast(rt, ftrt, INVOKE(name, arguments, ATTRIBUTE(expr)));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != rt.shape(); ++i) {
                items.add(cast(rt.dimension(i), ftrt.dimension(i), INVOKE(name + "#" + i, arguments, ATTRIBUTE(expr))));
            }
            return new FauxTuple(items);
        }
    }

    @Override
    public Expr constructIndirectInvoke(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments) {
        // Extract (concrete) type signature
        WyilFile.Type.Callable ft = expr.getSource().getType().as(WyilFile.Type.Callable.class);
        WyilFile.Type ftrt = ft.getReturn();
        boolean method = (ft instanceof WyilFile.Type.Method);
        // Extract (concrete) return type
        WyilFile.Type rt = expr.getType();
        // Identify any holes
        Tuple<WyilFile.Template.Variable> holes = WyilUtils.extractTemplate(ft,meter);
        // Determine the target name
        String name = toLambdaMangle(ft);
        // Apply conversions to arguments as necessary
        arguments = cast(ft.getParameter(), expr.getArguments(), arguments);
        // Add lambda value
        arguments.add(0, source);
        // Add heap argument
        arguments.add(0,HEAP);
        // Add bindings
        for (WyilFile.Template.Variable hole : holes) {
            arguments.add(VAR(hole.getName().get()));
        }
        //
        if (rt.shape() == 1) {
            return cast(rt, ftrt, INVOKE(name, arguments, ATTRIBUTE(expr)));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != rt.shape(); ++i) {
                items.add(cast(rt.dimension(i), ftrt.dimension(i), INVOKE(name + "#" + i, arguments, ATTRIBUTE(expr))));
            }
            return new FauxTuple(items);
        }
    }

    private Expr constructIndirectFunctionInvoke(WyilFile.Expr.IndirectInvoke expr, Expr source,
                                                 List<Expr> arguments) {
        WyilFile.Type.Function type = expr.getSource().getType().as(WyilFile.Type.Function.class);
        WyilFile.Type ret = expr.getType();
        String base = "f_apply$";
        ArrayList<Expr> args = new ArrayList<>();
        args.add(CONST(0));
        args.add(source);
        // Box all arguments as this is strictly required
        args.addAll(box(type.getParameter(), arguments));
        // Unbox return since it's always boxed
        if (ret.shape() == 1) {
            return unbox(ret, INVOKE(base + arguments.size(), args, ATTRIBUTE(expr)));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != ret.shape(); ++i) {
                args.set(0, CONST(i));
                items.add(unbox(ret.dimension(i), INVOKE(base + arguments.size(), args)));
            }
            return new FauxTuple(items, ATTRIBUTE(expr));
        }
    }

    private Expr constructIndirectMethodInvoke(int index, WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments) {
        WyilFile.Type ret = expr.getType();
        // This is a side-effecting method invocation which would have been translated
        // previously.
        if (ret.shape() == 1) {
            return VAR("m#" + index, ATTRIBUTE(expr));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != ret.shape(); ++i) {
                items.add(VAR("m#" + index + "#" + i));
            }
            return new FauxTuple(items, ATTRIBUTE(expr));
        }
    }

    @Override
    public Expr constructLambdaAccess(WyilFile.Expr.LambdaAccess expr) {
        WyilFile.Decl.Callable c = expr.getLink().getTarget();
        // Determine the mangled name for the function in question
        String name = toMangledName(c);
        // Read out its "lambda" value
        return VAR(name + "#lambda", ATTRIBUTE(expr));
    }

    @Override
    public Expr constructNew(WyilFile.Expr.New expr, Expr operand) {
        // Box operand (as necessary)
        operand = box(expr.getOperand().getType(), operand);
        //
        return INVOKE("Ref#new", operand, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructNotEqual(WyilFile.Expr.NotEqual expr, Expr lhs, Expr rhs) {
        WyilFile.Type lhsT = expr.getFirstOperand().getType();
        WyilFile.Type rhsT = expr.getSecondOperand().getType();
        boolean boxing = !lhsT.equals(rhsT);
        //
        if (lhs instanceof FauxTuple) {
            List<Expr> ls = ((FauxTuple) lhs).getItems();
            List<Expr> rs = ((FauxTuple) rhs).getItems();
            Expr.Logical result = null;
            for (int i = 0; i != lhsT.shape(); ++i) {
                Expr l = ls.get(i);
                Expr r = rs.get(i);
                l = boxing ? box(lhsT.dimension(i), l) : l;
                r = boxing ? box(rhsT.dimension(i), r) : r;
                result = i == 0 ? NEQ(l, r, ATTRIBUTE(expr)) : OR(result, NEQ(l, r), ATTRIBUTE(expr));
            }
            // Done
            return result;
        } else if (boxing) {
            return NEQ(box(lhsT, lhs), box(rhsT, rhs), ATTRIBUTE(expr));
        } else {
            return NEQ(lhs, rhs, ATTRIBUTE(expr));
        }
    }

    @Override
    public Expr constructRecordAccess(WyilFile.Expr.RecordAccess expr, Expr source) {
        Expr field = VAR("$" + expr.getField().get());
        return unbox(expr.getType(), GET(source, field, ATTRIBUTE(expr)));
    }

    @Override
    public Expr constructRecordInitialiser(WyilFile.Expr.RecordInitialiser expr, List<Expr> operands) {
        WyilFile.Tuple<WyilFile.Expr> values = expr.getOperands();
        WyilFile.Tuple<WyilFile.Identifier> fields = expr.getFields();
        //
        Expr rec = VAR("Record#Empty");
        //
        for (int i = 0; i != operands.size(); ++i) {
            Expr ith = box(values.get(i).getType(), operands.get(i));
            String field = "$" + fields.get(i).get();
            rec = PUT(rec, VAR(field), ith, ATTRIBUTE(expr));
        }
        //
        return rec;
    }

    @Override
    public Expr constructTupleInitialiser(WyilFile.Expr.TupleInitialiser expr, List<Expr> operands) {
        // Cast operands
        operands = cast(expr.getType(),expr.getOperands(),operands);
        // NOTE: at this stage, we won't attempt to support general first-class tuples.
        return new FauxTuple(operands, ATTRIBUTE(expr));
    }

    @Override
    public Expr constructStaticVariableAccess(WyilFile.Expr.StaticVariableAccess expr) {
        WyilFile.Type declared = expr.getLink().getTarget().getType();
        WyilFile.Type actual = expr.getType();
        // Apply name mangling
        String name = toMangledName(expr.getLink().getTarget());
        // Done
        return cast(actual, declared, VAR(name, ATTRIBUTE(expr)));
    }

    @Override
    public Expr constructVariableAccess(WyilFile.Expr.VariableAccess expr) {
        WyilFile.Type declared = expr.getVariableDeclaration().getType();
        WyilFile.Type actual = expr.getType();
        // Determine mangled name of this variable
        String name = toVariableName(expr.getVariableDeclaration());
        //
        return cast(actual, declared, VAR(name, ATTRIBUTE(expr)));
    }

    // =========================================================================================
    // Side Effects & Well-Definedness
    // =========================================================================================

    /**
     * Flattern an expression which may contain one or more function or method calls.  In addition,
     * this extracts any necessary well-definedness checks and produces a "flat" expression (i.e. without
     * nested calls) along with zero or more statements.  For example:
     *
     * <pre>
     *     x = join(xs[0],xs[1])
     * </pre>
     *  This would produce something of the following form:
     * <pre>
     *     assert 0 <= 0 && 0 < length(xs)
     *     assert 0 <= 1 && 1 < length(xs)
     *     call t0 := join(xs[0],xs[1])
     *     t0
     * </pre>
     * Here, we see the supplementary statements are first, with <code>t0</code> being the final flat
     * expression.
     *
     * @param e
     * @return
     */
    public Pair<List<Stmt>, Expr> flatternImpureExpression(Expr e) {
        DefinednessExtractor extractor = new DefinednessExtractor() {
             @Override
            public List<Stmt.Assert> visitLogical(Expr e) {
                 if (e instanceof FauxTuple) {
                     FauxTuple ft = (FauxTuple) e;
                     List<Stmt.Assert> rs = BOTTOM();
                     for (Expr fe : ft.items) {
                         rs.addAll(super.visitExpression(fe));
                     }
                     return rs;
                 } else {
                     return super.visitLogical(e);
                 }
             }
        };
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Flatten expression
        Expr r = new AbstractExpressionTransform() {
            @Override
            public Expr.Logical visitLogical(Expr e) {
                if (e instanceof FauxTuple) {
                    FauxTuple ft = (FauxTuple) e;
                    ArrayList<Expr> rs = new ArrayList<>();
                    for (Expr fe : ft.items) {
                        rs.add(super.visitExpression(fe));
                    }
                    return new FauxTuple(rs);
                } else {
                    return super.visitLogical(e);
                }
            }
            @Override
            public Expr.Logical constructInvoke(Expr.Invoke expr, List<Expr> arguments) {
                SyntacticItem wyItem = expr.getAttribute(SyntacticItem.class);
                // Check whether this corresponds to Whiley invocation or not.
                if (wyItem instanceof WyilFile.Expr.Invoke) {
                    WyilFile.Expr.Invoke ivk = (WyilFile.Expr.Invoke) wyItem;
                    WyilFile.Type.Callable ft = ivk.getBinding().getConcreteType();
                    int returns = ivk.getType().shape();
                    // Determine name mangle for call
                    String name = toMangledName(ivk.getLink().getTarget());
                    // Check mangled name matches (otherwise is synthetic)
                    if(expr.getName().startsWith(name) && !(ft instanceof WyilFile.Type.Property)) {
                        // Strip HEAP argument
                        arguments.remove(0);
                        // Add all well-definedness checks
                        for (int i = 0; i != arguments.size(); ++i) {
                            Expr ith = arguments.get(i);
                            stmts.addAll(extractor.visitExpression(ith));
                        }
                        if (returns == 1) {
                            Expr.VariableAccess lval = VAR(TEMP((WyilFile.Expr) wyItem),expr.getAttributes());
                            // Add procedure call
                            stmts.add(CALL(name, lval, arguments, expr.getAttributes()));
                            // Return variable access
                            return lval;
                        } else {
                            // Determine invoke index
                            int n = Integer.valueOf(expr.getName().substring(name.length() + 1));
                            //
                            ArrayList lvals = new ArrayList<>();
                            for (int i = 0; i != returns; ++i) {
                                lvals.add(VAR(TEMP((WyilFile.Expr) wyItem, i),expr.getAttributes()));
                            }
                            //
                            if (n == 0) {
                                // Add procedure call only on first occurrence
                                stmts.add(CALL(name, lvals, arguments, expr.getAttributes()));
                            }
                            // Return variable access
                            return (Expr.VariableAccess) lvals.get(n);
                        }
                    }
                } else if(wyItem instanceof WyilFile.Expr.IndirectInvoke) {
                    WyilFile.Expr.IndirectInvoke ivk = (WyilFile.Expr.IndirectInvoke) wyItem;
                    WyilFile.Type.Callable ft = ivk.getSource().getType().as(WyilFile.Type.Callable.class);
                    int returns = ivk.getType().shape();
                    // Determine name mangle for call
                    String name = toLambdaMangle(ft);
                    // Check mangled name matches (otherwise is synthetic)
                    if (expr.getName().startsWith(name)) {
                        // Strip HEAP argument
                        arguments.remove(0);
                        // Add all well-definedness checks
                        for (int i = 0; i != arguments.size(); ++i) {
                            Expr ith = arguments.get(i);
                            stmts.addAll(extractor.visitExpression(ith));
                        }
                        if (returns == 1) {
                            Expr.VariableAccess lval = VAR(TEMP((WyilFile.Expr) wyItem),expr.getAttributes());
                            // Add procedure call
                            stmts.add(CALL(name, lval, arguments, expr.getAttributes()));
                            // Return variable access
                            return lval;
                        } else {
                            // Determine invoke index
                            int n = Integer.valueOf(expr.getName().substring(name.length() + 1));
                            //
                            ArrayList lvals = new ArrayList<>();
                            for (int i = 0; i != returns; ++i) {
                                lvals.add(VAR(TEMP((WyilFile.Expr) wyItem, i),expr.getAttributes()));
                            }
                            //
                            if (n == 0) {
                                // Add procedure call only on first occurrence
                                stmts.add(CALL(name, lvals, arguments, expr.getAttributes()));
                            }
                            // Return variable access
                            return (Expr.VariableAccess) lvals.get(n);
                        }
                    }
                } else if(wyItem instanceof WyilFile.Expr.New && expr.getName().equals("Ref#new")) {
                    Expr.VariableAccess lval = VAR(TEMP((WyilFile.Expr) wyItem),expr.getAttributes());
                    // Add procedure call
                    stmts.add(CALL(expr.getName(), lval, arguments, expr.getAttributes()));
                    // Return variable access
                    return lval;
                }
                return super.constructInvoke(expr, arguments);
            }
        }.visitExpression(e);
        // Extract well-definedness conditions
        stmts.addAll(extractor.visitExpression(r));
        // Done
        return new Pair<>(stmts, r);
    }

    /**
     * Flat a list of zero or more expressions which may contain nested calls.
     * Furthermore, there is an assumption that the expressions may be multi-expressions
     * and these are also flatterned out.
     *
     * @param es
     * @return
     */
    public Pair<List<Stmt>, List<Expr>> flatternImpureExpressions(List<Expr> es) {
        List<Stmt> stmts = new ArrayList<>();
        List<Expr> exprs = new ArrayList<>();
        for (Expr e : es) {
            Pair<List<Stmt>, Expr> f = flatternImpureExpression(e);
            stmts.addAll(f.first());
            Expr fe = f.second();
            if (fe instanceof FauxTuple) {
                exprs.addAll(((FauxTuple) fe).items);
            } else {
                exprs.add(fe);
            }
        }
        return new Pair<>(stmts, exprs);
    }

    public Pair<List<Stmt>, List<Expr>> flatternImpureExpressions(Expr e) {
        return flatternImpureExpressions(Arrays.asList(e));
    }

    public Expr.Logical flatternAsLogical(Expr.Logical e) {
        DefinednessExtractor extractor = new DefinednessExtractor();
        List<Stmt.Assert> assertions = extractor.visitExpression(e);
        // Extract the conditions
        List<Expr.Logical> es = map(assertions, a -> a.getCondition());
        es.add(e);
        return AND(es, e.getAttributes());
    }

    public List<Expr.Logical> flatternAsLogical(List e) {
        ArrayList<Expr.Logical> rs = new ArrayList<>();
        for (int i = 0; i != e.size(); ++i) {
            rs.add(flatternAsLogical((Expr.Logical) e.get(i)));
        }
        return rs;
    }

    // =========================================================================================
    // Type Conversion
    // =========================================================================================

    /**
     *  The top-level (boxed) type representing all possible values in Whiley.
     */
    public static final Type ANY = new Type.Synonym("Any");
    /**
     * The top-level type of types (used for templates)
     */
    public static final Type TYPE = new Type.Synonym("Type");
    /**
     * The type of all record fields used in the Whiley program.
     */
    public static final Type FIELD = new Type.Synonym("Field");
    /**
     * A user-defined type which used to represent Whiley reference values.
     */
    public static final Type REF = new Type.Synonym("Ref");
    /**
     * A user-defined type which used to represent Whiley lambda's (i.e. function pointers, etc).
     */
    public static final Type LAMBDA = new Type.Synonym("Lambda");
    /**
     * A dictionary mapping integers to arbitrary boxed values. This is used to represent Whiley arrays. Since it holds
     * boxed values, we must always box any value written into an array and unbox anything read out of it.
     */
    public static final Type INTMAP = new Type.Dictionary(Type.Int, ANY);
    /**
     * A dictionary mapping fields to arbitrary boxed values. This is used to represent Whiley records. Since it holds
     * boxed values, we must always box any value written into an record and unbox anything read out of it.
     */
    public static final Type FIELDMAP = new Type.Dictionary(FIELD, ANY);
    /**
     * A dictionary mapping references to arbitrary boxed values. This is used to represent the Whiley heap. Reference
     * values index into this to give the values held at location they refer. Unallocated cells must have the value
     * <code>Void</code> to indicate they are indeed unallocated.
     */
    public static final Type REFMAP = new Type.Dictionary(REF, ANY);

    /**
     * Convert a Whiley type into a Boogie type. The goal is maintain a close relationship between Whiley types and
     * Boogie types where possible. For example, the Whiley <code>int</code> type is represented directly as the Boogie
     * type <code>int</code>, and likewise for <code>bool</code>. However, some Whiley types have no correspondence in
     * Boogie. For example, the Whiley type <code>int|null</code> has no equivalent in Boogie and, instead, we employ
     * the <code>Value</code> type. Likewise, Whiley references have no correspondance in Boogie, and we employ a
     * user-defined type <code>Ref</code> for this purpose.
     *
     * @param type
     * @return
     */
    private Type constructType(WyilFile.Type type) {
        // NOTE: this could be moved into AbstractTranslator?
        switch (type.getOpcode()) {
            case WyilFile.TYPE_null:
                return ANY;
            case WyilFile.TYPE_bool:
                return Type.Bool;
            case WyilFile.TYPE_byte:
                return Type.BitVector8;
            case WyilFile.TYPE_int:
                return Type.Int;
            case WyilFile.TYPE_reference:
                return REF;
            case WyilFile.TYPE_universal:
                return ANY;
            case WyilFile.TYPE_nominal:
                return constructNominalType((WyilFile.Type.Nominal) type);
            case WyilFile.TYPE_array:
                // NOTE: could actually do better here? In principle, yes, but it would require
                // generating axioms that could accept different types for arrays.
                return INTMAP;
            case WyilFile.TYPE_record:
                return FIELDMAP;
            case WyilFile.TYPE_union:
                return ANY;
            case WyilFile.TYPE_property:
            case WyilFile.TYPE_function:
            case WyilFile.TYPE_method:
                return LAMBDA;
            default:
                throw new IllegalArgumentException("unknown type encoutnered (" + type.getClass().getName() + ")");
        }
    }

    private Type constructNominalType(WyilFile.Type.Nominal type) {
        // Apply name mangling
        String name = toMangledName(type.getLink().getTarget());
        // Done!
        return new Type.Synonym(name);
    }

    @Override
    public Stmt applyImplicitCoercion(wyil.lang.WyilFile.Type target, wyil.lang.WyilFile.Type source, Stmt expr) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("implement me");
    }


    // ==============================================================================
    // Axioms
    // ==============================================================================

    /**
     * Generate declarations for all axioms used within the Boogie translation.
     *
     * @return
     */
    private List<Decl> constructAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        //
        decls.addAll(constructCommentHeading("Preamble"));
        // Define the context-level
        decls.add(new Decl.Constant("Context#Level", Type.Int));
        // Define the top-level Whiley type which contains all others.
        decls.add(new Decl.TypeSynonym("Type", null));
        // Define the top-level HEAP variable
        decls.add(new Decl.Variable("HEAP", REFMAP));
        decls.addAll(constructAnyAxioms(wf));
        // Add all void axioms
        decls.addAll(constructVoidAxioms(wf));
        // Add all null axioms
        decls.addAll(constructNullAxioms(wf));
        // Add all bool axioms
        decls.addAll(constructBoolAxioms(wf));
        // Add all byte axioms
        decls.addAll(constructByteAxioms(wf));
        // Add all int axioms
        decls.addAll(constructIntAxioms(wf));
        // Add all array axioms
        decls.addAll(constructArrayAxioms(wf));
        // Add all record axioms
        decls.addAll(constructRecordAxioms(wf));
        // Add all array axioms
        decls.addAll(constructReferenceAxioms(wf));
        // Add all array axioms
        decls.addAll(constructLambdaAxioms(wf));
        // Add type exclusion axioms
        decls.addAll(constructExclusionAxioms(wf));
        // Add type constants
        decls.addAll(constructMetaTypeAxioms(wf));
        // Done
        return decls;
    }
    private List<Decl> constructAnyAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Any"));
        // Define the top-level Whiley value which contains all others.
        decls.add(new Decl.TypeSynonym("Any", null));
        //
        List<Decl.Parameter> parameters = Arrays.asList(HEAP_PARAM, new Decl.Parameter("p", REF), new Decl.Parameter("q", ANY));
        Expr.Logical refs = AND(INVOKE("Ref#is",VAR("q")),INVOKE("Ref#within",HEAP,VAR("p"),INVOKE("Ref#unbox",VAR("q"))));
        Expr.Logical arrs = AND(INVOKE("Array#is",VAR("q")),INVOKE("Array#within",HEAP,VAR("p"),INVOKE("Array#unbox",VAR("q"))));
        Expr.Logical recs = AND(INVOKE("Record#is",VAR("q")),INVOKE("Record#within",HEAP,VAR("p"),INVOKE("Record#unbox",VAR("q"))));
        decls.add(FUNCTION("Any#within", parameters, Type.Bool, OR(refs, arrs, recs)));
        //
        return decls;
    }
    private List<Decl> constructVoidAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Void"));
        // Add null constant
        decls.add(new Decl.Constant(true, "Void", ANY));
        decls.add(FUNCTION("Void#is", new Decl.Parameter("v", ANY), Type.Bool, EQ(VAR("v"), VOID)));
        //
        return decls;
    }

    private List<Decl> constructNullAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Null"));
        // Add null constant
        decls.add(new Decl.Constant(true, "Null", ANY));
        decls.add(FUNCTION("Null#is", new Decl.Parameter("v", ANY), Type.Bool, EQ(VAR("v"), VAR("Null"))));
        //
        return decls;
    }

    /**
     * Construct axioms and functions relevant to integer types.
     *
     * @param wf
     * @return
     */
    private List<Decl> constructBoolAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Booleans"));
        decls.add(FUNCTION("Bool#box", Type.Bool, ANY));
        decls.add(FUNCTION("Bool#unbox", ANY, Type.Bool));
        decls.add(FUNCTION("Bool#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("b", Type.Bool, EQ(INVOKE("Bool#box", VAR("b")), VAR("v")))));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(FORALL("b", Type.Bool, EQ(INVOKE("Bool#unbox", INVOKE("Bool#box", VAR("b"))), VAR("b")))));
        // Establish no connection between bools and Void
        decls.add(new Decl.Axiom(FORALL("b", Type.Bool, NEQ(INVOKE("Bool#box", VAR("b")), VOID))));
        // Done
        return decls;
    }

    /**
     * Construct axioms and functions relevant to integer types.
     *
     * @param wf
     * @return
     */
    private List<Decl> constructIntAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Integers"));
        decls.add(FUNCTION("Int#box", Type.Int, ANY));
        decls.add(FUNCTION("Int#unbox", ANY, Type.Int));
        decls.add(FUNCTION("Int#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("i", Type.Int, EQ(INVOKE("Int#box", VAR("i")), VAR("v")))));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(
                FORALL("i", Type.Int, EQ(INVOKE("Int#unbox", INVOKE("Int#box", VAR("i"))), VAR("i")))));
        // Establish no connection between ints and Void
        decls.add(new Decl.Axiom(FORALL("i", Type.Int, NEQ(INVOKE("Int#box", VAR("i")), VOID))));
        // Done
        return decls;
    }

    /**
     * Construct axioms and functions relevant to byte types.
     *
     * @param wf
     * @return
     */
    private List<Decl> constructByteAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Bytes"));
        decls.add(FUNCTION("Byte#box", Type.BitVector8, ANY));
        decls.add(FUNCTION("Byte#unbox", ANY, Type.BitVector8));
        decls.add(FUNCTION("Byte#toInt", Type.BitVector8, Type.Int, ":bvbuiltin", "\"bv2int\""));
        decls.add(FUNCTION("Byte#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("b", Type.BitVector8, EQ(INVOKE("Byte#box", VAR("b")), VAR("v")))));
        // NOTE: figuring out int2bv was a challenge!
        decls.add(FUNCTION("Byte#fromInt", Type.Int, Type.BitVector8, ":bvbuiltin", "\"(_ int2bv 8)\""));
        decls.add(FUNCTION("Byte#Not", Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvnot\""));
        decls.add(FUNCTION("Byte#And", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvand\""));
        decls.add(FUNCTION("Byte#Or", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvor\""));
        decls.add(FUNCTION("Byte#Xor", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvxor\""));
        decls.add(FUNCTION("Byte#Shl", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvshl\""));
        decls.add(FUNCTION("Byte#Shr", Type.BitVector8, Type.BitVector8, Type.BitVector8, ":bvbuiltin", "\"bvlshr\""));
        // Establish connection between tbox and unbox
        decls.add(new Decl.Axiom(
                FORALL("b", Type.BitVector8, EQ(INVOKE("Byte#unbox", INVOKE("Byte#box", VAR("b"))), VAR("b")))));
        // Establish no connection between bytes and Void
        decls.add(new Decl.Axiom(FORALL("b", Type.BitVector8, NEQ(INVOKE("Byte#box", VAR("b")), VOID))));
        // Done
        return decls;
    }

    /**
     * Construct axioms relevant to array types.
     *
     * @return
     */
    private List<Decl> constructArrayAxioms(WyilFile wf) {
        // A few helpers
        final Expr i = VAR("i");
        final Expr v = VAR("v");
        final Expr a = VAR("a");
        final Expr l = VAR("l");
        // NOTE: we could reduce the amount of boxing / unboxing necessary by generating
        // custom array types for each different array type encountered.
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Arrays"));
        decls.add(FUNCTION("Array#box", INTMAP, ANY));
        decls.add(FUNCTION("Array#unbox", ANY, INTMAP));
        decls.add(FUNCTION("Array#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("a", INTMAP, EQ(INVOKE("Array#box", a), v))));
        // Array index is in bounds
        List<Decl.Parameter> parameters = Arrays.asList(new Decl.Parameter("a", INTMAP), new Decl.Parameter("i", Type.Int));
        decls.add(FUNCTION("Array#in", parameters, Type.Bool,
                AND(GTEQ(VAR("i"), CONST(0)), LT(i, INVOKE("Array#Length", a)))));
        // Establish connection between tbox and unbox
        decls.add(new Decl.Axiom(FORALL("i", INTMAP, EQ(INVOKE("Array#unbox", INVOKE("Array#box", i)), i))));
        // Establish no connection between arrays and Void
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, NEQ(INVOKE("Array#box", a), VOID))));
        // Array length function
        decls.add(FUNCTION("Array#Length", INTMAP, Type.Int));
        // Enforce array length is non-negative
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, LTEQ(CONST(0), INVOKE("Array#Length", a)))));
        // Relate updated array with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "i", Type.Int, "v", ANY,
                IMPLIES(AND(NEQ(v, VOID), INVOKE("Array#in", a, i)),
                        EQ(INVOKE("Array#Length", a), INVOKE("Array#Length", PUT(a, i, v)))))));
        // Empty arrays
        decls.add(new Decl.LineComment("Array Initialisers"));
        decls.add(FUNCTION("Array#Empty", Type.Int, INTMAP));
        // Ensure that all elements outside array length are void
        decls.add(new Decl.Axiom(
                FORALL("l", Type.Int, "i", Type.Int, OR(AND(LTEQ(CONST(0), i), LT(i, l)),
                        EQ(GET(INVOKE("Array#Empty", l), i), VOID)))));
        // Ensure that all elements inside array length are not void
        decls.add(new Decl.Axiom(
                FORALL("l", Type.Int, "i", Type.Int, IMPLIES(AND(LTEQ(CONST(0), i), LT(i, l)),
                        NEQ(GET(INVOKE("Array#Empty", l), i), VOID)))));
        // Relate empty array with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "l", Type.Int,
                IMPLIES(AND(LTEQ(CONST(0),l),EQ(INVOKE("Array#Empty", l), a)), EQ(INVOKE("Array#Length", a), l)))));
        // Array generators
        decls.add(new Decl.LineComment("Array Generators"));
        decls.add(FUNCTION("Array#Generator", ANY, Type.Int, INTMAP));
        // Ensure that all elements inside generator length are void
        decls.add(new Decl.Axiom(FORALL("v", ANY, "l", Type.Int, "i", Type.Int, IMPLIES(AND(LTEQ(CONST(0),i),
                LT(i, l), NEQ(v, VOID)), EQ(GET(INVOKE("Array#Generator", v, l), i), v)))));
        // Ensure that all elements outside generator length are void
        decls.add(new Decl.Axiom(FORALL("v", ANY, "l", Type.Int, "i", Type.Int,
                OR(AND(LTEQ(CONST(0), i), LT(i, l)),
                        EQ(GET(INVOKE("Array#Generator", v, l), i), VOID)))));
        // Relate array generator with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "v", ANY, "l", Type.Int,
                IMPLIES(AND(LTEQ(CONST(0),l), EQ(INVOKE("Array#Generator", v, l), a)),
                        EQ(INVOKE("Array#Length", a), l)))));
        // Possible update for this axiom
//        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "i", Type.Int, "v", ANY,
//                OR(EQ(v, VOID), EQ(INVOKE("Array#Length", a), INVOKE("Array#Length", PUT(a, i, v)))))));
        // is p within this array
        parameters = Arrays.asList(HEAP_PARAM, new Decl.Parameter("p", REF), new Decl.Parameter("q", INTMAP));
        decls.add(FUNCTION("Array#within", parameters, Type.Bool, EXISTS("i", Type.Int, INVOKE("Any#within", HEAP, VAR("p"), GET(VAR("q"), i)))));
        // Done
        return decls;
    }

    /**
     * Construct axioms relevant to record types. An import issue is to determine the full set of field names which are
     * in play.
     *
     * @return
     */
    private List<Decl> constructRecordAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Fields"));
        // Defines the type of all fields
        decls.add(new Decl.TypeSynonym("Field", null));
        // Add all known field names
        for (String field : determineFieldNames(wf)) {
            String name = "$" + field;
            decls.add(new Decl.Constant(true, name, FIELD));
        }
        //
        decls.addAll(constructCommentSubheading("Records"));
        decls.add(FUNCTION("Record#box", FIELDMAP, ANY));
        decls.add(FUNCTION("Record#unbox", ANY, FIELDMAP));
        // FIXME: something tells me we should be considering a field count here.
        decls.add(FUNCTION("Record#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("r", FIELDMAP, EQ(INVOKE("Record#box", VAR("r")), VAR("v")))));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(
                FORALL("i", FIELDMAP, EQ(INVOKE("Record#unbox", INVOKE("Record#box", VAR("i"))), VAR("i")))));
        // Establish no connection between records and Void
        decls.add(new Decl.Axiom(FORALL("r", FIELDMAP, NEQ(INVOKE("Record#box", VAR("r")), VOID))));
        // Defines the empty record (i.e. the base from which all other records are
        // constructed).
        decls.add(new Decl.Constant(true, "Record#Empty", FIELDMAP));
        decls.add(new Decl.Axiom(FORALL("f", FIELD, EQ(GET(VAR("Record#Empty"), VAR("f")), VOID))));
        // is p within this record
        List<Decl.Parameter> parameters = Arrays.asList(HEAP_PARAM, new Decl.Parameter("p", REF), new Decl.Parameter("q", FIELDMAP));
        decls.add(FUNCTION("Record#within", parameters, Type.Bool, EXISTS("f", FIELD, INVOKE("Any#within", HEAP, VAR("p"), GET(VAR("q"), VAR("f"))))));
        // Done
        return decls;
    }

    /**
     * Construct axioms and functions relevant to reference types.
     *
     * @param wf
     * @return
     */
    private List<Decl> constructReferenceAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("References"));
        decls.add(new Decl.TypeSynonym("Ref", null));
        decls.add(FUNCTION("Ref#box", REF, ANY));
        decls.add(FUNCTION("Ref#unbox", ANY, REF));
        decls.add(FUNCTION("Ref#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("r", REF, EQ(INVOKE("Ref#box", VAR("r")), VAR("v")))));
        decls.add(new Decl.Constant(true, "Ref#Empty", REFMAP));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(
                FORALL("r", REF, EQ(INVOKE("Ref#unbox", INVOKE("Ref#box", VAR("r"))), VAR("r")))));
        // Establish no connection between references and Void
        decls.add(new Decl.Axiom(FORALL("r", REF, NEQ(INVOKE("Ref#box", VAR("r")), VOID))));
        // Construct the allocation procedure
        Expr.VariableAccess val = VAR("val");
        Expr.VariableAccess ref = VAR("ref");
        //
        List<Decl.Parameter> parameters = Arrays.asList(
                new Decl.Parameter(val.getVariable(), ANY));
        List<Decl.Parameter> returns = Arrays.asList(
                new Decl.Parameter(ref.getVariable(), REF));
        // FIXME: there are still some problems below related to the Void constant which
        // is not necessarily disjoint with all integer constants, etc.
        List<Expr.Logical> requires = new ArrayList<>();
        List<Expr.Logical> ensures = new ArrayList<>();
        // Heap location at ref equals val
        ensures.add(EQ(GET(HEAP, ref), val));
        // Heap location not previously allocated!
        ensures.add(EQ(GET(OLD_HEAP, ref), VOID));
        // All allocated locations remain as before
        ensures.add(FORALL("r", REF, OR(EQ(ref, VAR("r")), EQ(GET(OLD_HEAP, VAR("r")), GET(HEAP, VAR("r"))))));
        //
        decls.add(new Decl.Procedure("Ref#new", parameters, returns, requires, ensures, Arrays.asList("HEAP")));
        // is p within this reference?
        parameters = Arrays.asList(HEAP_PARAM, new Decl.Parameter("p", REF), new Decl.Parameter("q", REF));
        decls.add(FUNCTION("Ref#within", parameters, Type.Bool, OR(EQ(VAR("p"), VAR("q")), INVOKE("Any#within", HEAP, VAR("p"), GET(HEAP, VAR("q"))))));
        // Done
        return decls;
    }

    private List<Decl> constructLambdaAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Lambdas"));
        decls.add(new Decl.TypeSynonym("Lambda", null));
        decls.add(FUNCTION("Lambda#box", LAMBDA, ANY));
        decls.add(FUNCTION("Lambda#unbox", ANY, LAMBDA));
        decls.add(FUNCTION("Lambda#return", LAMBDA, Type.Int, ANY));
        decls.add(FUNCTION("Lambda#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("l", LAMBDA, EQ(INVOKE("Lambda#box", VAR("l")), VAR("v")))));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(
                FORALL("l", LAMBDA, EQ(INVOKE("Lambda#unbox", INVOKE("Lambda#box", VAR("l"))), VAR("l")))));
        // Establish no connection between lambdas and Void
        decls.add(new Decl.Axiom(FORALL("l", LAMBDA, NEQ(INVOKE("Lambda#box", VAR("l")), VOID))));
        // Extract all lambda types used anyway
        Set<WyilFile.Type.Callable> types = extractLambdaTypes(wf);
        //
        for(WyilFile.Type.Callable t : types) {
            decls.addAll(constructFunctionOrMethodLambda(t));
        }
        // done
        return decls;
    }

    private List<Decl> constructFunctionOrMethodLambda(WyilFile.Type.Callable mt) {
        boolean method = (mt instanceof WyilFile.Type.Method);
        Tuple<WyilFile.Template.Variable> holes = WyilUtils.extractTemplate(mt,meter);
        //
        String name = toLambdaMangle(mt);
        ArrayList<Decl> decls = new ArrayList<>();
        decls.add(new Decl.LineComment(mt.toString()));
        WyilFile.Type parameterType = mt.getParameter();
        WyilFile.Type returnType = mt.getReturn();
        // Translate parameter and return types
        Pair<List<Decl.Parameter>, List<Expr.Logical>> ps = constructAnonymousParameters("p", parameterType, HEAP);
        Pair<List<Decl.Parameter>, List<Expr.Logical>> rs = constructAnonymousParameters("r", returnType, HEAP);
        List<Decl.Parameter> parameters = ps.first();
        List<Decl.Parameter> returns = rs.first();
        List<Expr.Logical> precondition = ps.second();
        List<Expr.Logical> postcondition = rs.second();
        // Add lambda reference parameter
        parameters.add(0, new Decl.Parameter("l", LAMBDA));
        {
            int i = 2;
            for (WyilFile.Template.Variable hole : holes) {
                parameters.add(i++, new Decl.Parameter(hole.getName().get(), TYPE));
            }
        }
        // Add connection to lambda reference
        // FIXME: what is this for?
        for (int i = 0; i < returnType.shape(); ++i) {
            postcondition.add(EQ(box(returnType.dimension(i), VAR("r#" + i)), INVOKE("Lambda#return", VAR("l"), CONST(i))));
        }
        List<String> modifies = Collections.EMPTY_LIST;
        if(method) {
            // Add frame axioms
            postcondition.addAll(constructMethodFrame(mt, i -> ("p#" + i), i -> ("r#" + i), mt));
            // Specific modifies heap
            modifies = Arrays.asList("HEAP");
        } else {
            ArrayList<Decl.Parameter> f_params = new ArrayList<>(parameters);
            f_params.add(0,HEAP_PARAM);
            List<Expr> f_args = map(f_params, p -> VAR(p.getName()));
            List<Expr> f_rets = map(returns, p -> VAR(p.getName()));
            // Add function prototype
            switch (returns.size()) {
                case 0:
                    decls.add(FUNCTION(name, f_params, ANY));
                    break;
                case 1: {
                    Type rt = returns.get(0).getType();
                    decls.add(FUNCTION(name, f_params, rt));
                    // Establish connection
                    postcondition.add(EQ(INVOKE(name,f_args),f_rets.get(0)));
                    break;
                }
                default: {
                    // Multiple returns require special handling
                    for (int i = 0; i != returns.size(); ++i) {
                        Type rt = returns.get(i).getType();
                        decls.add(FUNCTION(name + "#" + i, f_params, rt));
                        // Establish connection
                        postcondition.add(EQ(INVOKE(name + "#" + i,f_args),f_rets.get(i)));
                    }
                }
            }
        }
        // Add heap for method invocations
        decls.add(new Decl.Procedure(name, parameters, returns, precondition, postcondition, modifies));
        //
        return decls;
    }

    private List<Decl> constructExclusionAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Exclusions"));
        String[] types = {"Null", "Byte", "Bool", "Int", "Array", "Record", "Ref", "Lambda"};
        Expr.VariableAccess var = VAR("v");
        //
        for (int i = 0; i != types.length; ++i) {
            Expr.Logical[] negs = new Expr.Logical[types.length - 1];
            for (int j = 0, k = 0; j != types.length; ++j) {
                if (j != i) {
                    negs[k++] = NOT(INVOKE(types[j] + "#is", var));
                }
            }
            Expr.Logical pos = INVOKE(types[i] + "#is", var);
            decls.add(new Decl.Axiom(FORALL("v", ANY, IMPLIES(pos, AND(negs)))));
        }
        return decls;
    }

    private List<Decl> constructMetaTypeAxioms(WyilFile f) {
        ArrayList<Decl> decls = new ArrayList<>();
        // Add useful comment
        decls.addAll(constructCommentSubheading("Meta Types"));
        decls.add(FUNCTION("Type#is",REFMAP,TYPE,ANY,Type.Bool));
        // Extract all types used in a meta-type position
        Set<WyilFile.Type> types = extractMetaTypes(f);
        //
        for (WyilFile.Type type : types) {
            // Extract all holes
            Tuple<WyilFile.Template.Variable> holes = WyilUtils.extractTemplate(type, meter);
            // Act accordingly
            if (type instanceof WyilFile.Type.Universal) {
                // Always substituted directly
            } else if (holes.size() == 0) {
                // Construct meta constant
                String name = "Type#" + getMangle(type);
                decls.add(new Decl.Constant(true, name, TYPE));
                // Construct a suitable type test
                Expr.Logical test = constructTypeTest(type, WyilFile.Type.Any, VAR("v"), HEAP, type);
                ArrayList<Decl.Parameter> params = new ArrayList<>();
                params.add(new Decl.Parameter("v", ANY));
                params.add(0, HEAP_PARAM);
                // Assert relationship between constant and type test
                decls.add(new Decl.Axiom(FORALL(params, IFF(INVOKE("Type#is", HEAP, VAR(name), VAR("v")), test))));
            } else {
                String name = "Type#" + getMangle(type);
                ArrayList<Decl.Parameter> params = new ArrayList<>();
                ArrayList<Expr> args = new ArrayList<>();
                for (WyilFile.Template.Variable t : holes) {
                    String n = t.getName().get();
                    params.add(new Decl.Parameter(n, TYPE));
                    args.add(VAR(n));
                }
                decls.add(FUNCTION(name, params, TYPE));
                Expr ivk = INVOKE(name, args);
                // Construct a suitable type test
                Expr.Logical test = constructTypeTest(type, WyilFile.Type.Any, VAR("v"), HEAP, type);
                params.add(new Decl.Variable("v", ANY));
                // Assert relationship between constant and type test
                params.add(0, HEAP_PARAM);
                decls.add(new Decl.Axiom(FORALL(params, IFF(INVOKE("Type#is", HEAP, ivk, VAR("v")), test))));
            }
        }

        return decls;
    }

    // ==============================================================================
    // Lambda Type Extraction
    // ==============================================================================

    private Set<WyilFile.Type.Callable> extractLambdaTypes(WyilFile f) {
        HashSet<WyilFile.Type.Callable> lambdas = new HashSet<>();
        for (WyilFile.Decl.Unit unit : f.getModule().getUnits()) {
            extractLambdaTypes(unit, lambdas);
        }
        return lambdas;
    }

    private void extractLambdaTypes(WyilFile.Decl.Unit unit, Set<WyilFile.Type.Callable> lambdas) {
        HashSet<WyilFile.Type> visited = new HashSet<>();
        //
        new AbstractVisitor(meter) {
            @Override
            public void visitIndirectInvoke(WyilFile.Expr.IndirectInvoke expr) {
                super.visitIndirectInvoke(expr);
                WyilFile.Type.Callable type = expr.getSource().getType().as(WyilFile.Type.Callable.class);
                lambdas.add(type);
            }
        }.visitUnit(unit);
    }

    // ==============================================================================
    // Meta Type Extraction
    // ==============================================================================

    private Set<WyilFile.Type> extractMetaTypes(WyilFile f) {
        HashSet<WyilFile.Type> metas = new HashSet<>();
        for (WyilFile.Decl.Unit unit : f.getModule().getUnits()) {
            extractMetaTypes(unit, metas);
        }
        for (WyilFile.Decl.Unit unit : f.getModule().getExterns()) {
            extractMetaTypes(unit, metas);
        }
        return metas;
    }

    private void extractMetaTypes(WyilFile.Decl.Unit unit, Set<WyilFile.Type> metas) {
        // Always include void
        metas.add(WyilFile.Type.Void);
        //
        HashSet<WyilFile.Type> visited = new HashSet<>();
        new AbstractVisitor(meter) {
            @Override
            public void visitTypeNominal(WyilFile.Type.Nominal type) {
                WyilFile.Type concrete = type.getConcreteType();
                if (visited.contains(concrete)) {
                    return;
                } else {
                    // Record visited this type to protect against infinite loops
                    visited.add(concrete);
                    // Continue traversing contents
                    super.visitTypeNominal(type);
                    // Extract binding (if any)
                    Tuple<WyilFile.Type> binding = type.getParameters();
                    //
                    for (WyilFile.Type t : binding) {
                        metas.add(t);
                    }
                }
            }
            @Override
            public void visitTypeReference(WyilFile.Type.Reference type) {
                super.visitTypeReference(type);
                // Add element type to help reasoning about the heap.
                metas.add(type.getElement());
            }
            @Override
            public void visitInvoke(WyilFile.Expr.Invoke expr) {
                super.visitInvoke(expr);
                // Extract binding (if any)
                Tuple<WyilFile.Type> binding = expr.getBinding().getArguments();
                // Add them all
                for (WyilFile.Type t : binding) {
                    metas.add(t);
                }
            }

        }.visitUnit(unit);
    }

    // ==============================================================================
    // Type Invariant Extraction
    // ==============================================================================

    /**
     * Extract any constraints from a given type which must be enforced. If no such constraints exist, simple return
     * <code>null</code>. For example, consider the following:
     *
     * <pre>
     * type nat is (int n) where n >= 0
     *
     * function f(nat x) -> int:
     *    ...
     * </pre>
     * <p>
     * The type <code>nat</code> yields a constraint <code>x >= 0</code> for the given parameter which should be added
     * as a precondition.
     *
     * @param type The type from which constraints are being generated
     * @param expr An expression representing the item being constrained (e.g. a parameter or local variable).
     * @return
     */
    private Expr.Logical constructTypeConstraint(WyilFile.Type type, Expr expr, Expr heap, SyntacticItem item) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_null:
            case WyilFile.TYPE_bool:
            case WyilFile.TYPE_byte:
            case WyilFile.TYPE_int:
                // No constraints exist on primitive types.
                return null;
            default:
                // Fall back to primitive test
                return constructTypeTest(type, type, expr, heap, item);
        }
    }

    /**
     * Construct a sequence of zero or more constraints arising from zero or more variables.
     *
     * @param vars
     * @param heap
     * @return
     */
    private List<Expr.Logical> constructTypeConstraints(Tuple<WyilFile.Decl.Variable> vars, Expr heap) {
        List<Expr.Logical> constraints = new ArrayList<>();
        for (int i = 0; i != vars.size(); ++i) {
            WyilFile.Decl.Variable ith = vars.get(i);
            Expr.Logical c = constructTypeConstraint(ith.getType(), VAR(toVariableName(ith)), heap, ith);
            if (c != null) {
                constraints.add(c);
            }
        }
        return constraints;
    }

    // ==============================================================================
    // Runtime Type Tests
    // ==============================================================================

    /**
     * Construct a runtime type test for a given argument operand. For example, consider the following:
     *
     * <pre>
     * func)tion f(int|null x) -> (int r):
     *   if x is null:
     *      return 0
     *   else:
     *      return x
     * </pre>
     * <p>
     * The expression <code>x is null</code> will be translated by this function.  This function assumes the argument has the `from` type.
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructTypeTest(WyilFile.Type to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        switch (to.getOpcode()) {
            case WyilFile.TYPE_any:
                return NEQ(box(from, argument), VOID, ATTRIBUTE(item));
            case WyilFile.TYPE_void:
                return INVOKE("Void#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_null:
                return INVOKE("Null#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_bool:
                return INVOKE("Bool#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_byte:
                return INVOKE("Byte#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_int:
                return INVOKE("Int#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_universal:
                return constructUniversalTypeTest((WyilFile.Type.Universal) to, from, argument, heap, item);
            case WyilFile.TYPE_property:
                return INVOKE("Lambda#is", box(from, argument), ATTRIBUTE(item));
            case WyilFile.TYPE_function:
                return constructFunctionTypeTest((WyilFile.Type.Function) to, from, argument, heap, item);
            case WyilFile.TYPE_method:
                return constructMethodTypeTest((WyilFile.Type.Method) to, from, argument, heap, item);
            case WyilFile.TYPE_nominal:
                return constructNominalTypeTest((WyilFile.Type.Nominal) to, from, argument, heap, item);
            case WyilFile.TYPE_array:
                return constructArrayTypeTest((WyilFile.Type.Array) to, from, argument, heap, item);
            case WyilFile.TYPE_record:
                return constructRecordTypeTest((WyilFile.Type.Record) to, from, argument, heap, item);
            case WyilFile.TYPE_reference:
                return constructReferenceTypeTest((WyilFile.Type.Reference) to, from, argument, heap, item);
            case WyilFile.TYPE_union:
                return constructUnionTypeTest((WyilFile.Type.Union) to, from, argument, heap, item);
            default:
                throw new IllegalArgumentException("unknown type encoutnered (" + to.getClass().getName() + ")");
        }
    }

    /**
     * Specialisation of <code>constructTypeTest()</code> when <code>to</code> and <code>from</code> types are known to be the same.
     *
     * @param type
     * @param argument
     * @param heap
     * @param item
     * @return
     */
    private Expr.Logical constructTypeTest(WyilFile.Type type, Expr argument, Expr heap, SyntacticItem item) {
         switch (type.getOpcode()) {
             case WyilFile.TYPE_bool:
             case WyilFile.TYPE_byte:
             case WyilFile.TYPE_int:
             case WyilFile.TYPE_universal:
                 return CONST(true);
         }
        return constructTypeTest(type, type, argument, heap, item);
    }


    /**
     * Construct a type test for a nominal type. This is done by simple calling the
     * <code>is</code> method for the corresponding nominal type. For example,
     * consider the following:
     *
     * <pre>
     * type nat is (int x) where ...
     *
     *   ...
     *   if x is nat:
     *      ...
     * </pre>
     * <p>
     * For the type <code>nat</code> we will generate:
     *
     * <pre>
     * function nat#is(Value v) { ... }
     * </pre>
     * <p>
     * And we can translate <code>x is nat</code> as a call to this function.
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructNominalTypeTest(WyilFile.Type.Nominal to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        ArrayList<Expr> arguments = new ArrayList<>();
        // Extract template binding
        Tuple<WyilFile.Type> binding = to.getParameters();
        // Construct appropriate name mangle
        String name = toMangledName(to.getLink().getTarget());
        // Add template parameters (if applicable)
        for (int i = 0; i != binding.size(); ++i) {
            arguments.add(i,constructMetaType(binding.get(i), heap));
        }
        // Add remaining parameters
        arguments.add(box(from, argument));
        // Add heap argument for impure type
        arguments.add(heap);
        // Ensure argument is boxed!
        return INVOKE(name + "#is", arguments, ATTRIBUTE(item));
    }

    public Expr.Logical constructUniversalTypeTest(WyilFile.Type.Universal to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        return AND(NEQ(argument, VOID),
                INVOKE("Type#is", heap, VAR(to.getOperand().get()), argument, ATTRIBUTE(item)));
    }

    /**
     * Construct a type test for an unadorned record type. For simplicity, this is done inline. For example:
     *
     * <pre>
     *   ...
     *   if x is {int f, bool g}:
     *      ...
     * </pre>
     * <p>
     * Then, the <code>is</code> expression is translated as:
     *
     * <pre>
     *   Int#is(x[f]) && Bool#is(x[g])
     * </pre>
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructRecordTypeTest(WyilFile.Type.Record to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        // NOTE: this method for describing a type test should be deprecated in the
        // future in favour of something based around type tags.
        Expr.VariableAccess v = VAR(TEMP("f"));
        //
        Tuple<WyilFile.Type.Field> fields = to.getFields();
        Expr.Logical[] inclauses = new Expr.Logical[fields.size()];
        Expr.Logical[] outclauses = new Expr.Logical[fields.size()];
        // Cast argument to correct (unboxed) type
        Expr nArgument = cast(to, from, argument);
        // Iterate fields constructing tests for each.
        for (int i = 0; i != inclauses.length; ++i) {
            WyilFile.Type.Field f = fields.get(i);
            String field = "$" + f.getName().get();
            inclauses[i] = constructTypeTest(f.getType(), WyilFile.Type.Any, GET(nArgument, VAR(field)), heap, item);
            outclauses[i] = NEQ(VAR(field),v);
        }
        // Combine indivudal cases
        Expr.Logical test = AND(inclauses, ATTRIBUTE(item));
        // Construct type test (when necessary)
        Expr.Logical inbound = argument != nArgument ? AND(INVOKE("Record#is", argument), test, ATTRIBUTE(item)) : test;
        Expr.Logical outbound = FORALL(v.getVariable(), FIELD, IMPLIES(AND(outclauses), EQ(GET(nArgument, v), VOID)));
        // Finally, apply outbounds to closed records only since these are the ones whose fields we actually know about.
        return to.isOpen() ?  inbound : AND(inbound, outbound, ATTRIBUTE(item));
    }

    /**
     * Construct a type test for an unadorned array type. For simplicity, this is done inline. For example:
     *
     * <pre>
     *   ...
     *   if x is int[]:
     *      ...
     * </pre>
     * <p>
     * Then, the <code>is</code> expression is translated as:
     *
     * <pre>
     *   (forall i:int :: 0 <= i && i < length(x) ==> Int#is(x[i]))
     * </pre>
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param nArgument The argument being tested.
     * @return
     */
    private Expr.Logical constructArrayTypeTest(WyilFile.Type.Array to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        // Generate temporary index variable (which avoids name clashes). Observe that we cannot use the index in this
        // case, because types are not guaranteed to be part of the heap.  For example, when they are constructed for
        // generic nominal types.
        Expr.VariableAccess i = VAR(TEMP("i"));
        // Cast argument to (unboxed) array type
        Expr nArgument = cast(to, from, argument);
        // Construct bounds check for index variable
        Expr.Logical inbounds = INVOKE("Array#in", nArgument, i);
        // Construct (out of) bounds check for index variable
        Expr.Logical outbounds = NOT(inbounds);
        // Recursively construct type test for element
        Expr.Logical valid = constructTypeTest(to.getElement(), WyilFile.Type.Any, GET(nArgument, i), heap, item);
        // Elements outside range equal void
        Expr.Logical invalid = EQ(GET(nArgument,i),VOID);
        // Construct concrete test
        Expr.Logical test = FORALL(i.getVariable(), Type.Int, AND(IMPLIES(inbounds, valid), IMPLIES(outbounds, invalid)), ATTRIBUTE(item));
        // Construct type test (when necessary)
        return argument != nArgument ? AND(INVOKE("Array#is", argument), test, ATTRIBUTE(item)) : test;
    }

    private Expr.Logical constructReferenceTypeTest(WyilFile.Type.Reference to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        heap = (heap == null) ? EMPTY_HEAPVAR : heap;
        // Cast argument to (unboxed) reference type
        Expr nArgument = cast(to, from, argument);
        // Dereference argument
        Expr deref = GET(heap, nArgument);
        // Construct element type test
        Expr.Logical test = constructTypeTest(to.getElement(), WyilFile.Type.Any, deref, heap, item);
        // Construct type test (when necessary)
        return argument != nArgument ? AND(INVOKE("Ref#is", argument), test, ATTRIBUTE(item)) : test;
    }

    /**
     * Construct a type test for an unadorned union type. For simplicity, this is done inline using disjunctions. For
     * example:
     *
     * <pre>
     *   ...
     *   if x is int|null:
     *      ...
     * </pre>
     * <p>
     * Then, the <code>is</code> expression is translated as:
     *
     * <pre>
     *   Int#is(x[i]) || x == null
     * </pre>
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructUnionTypeTest(WyilFile.Type.Union to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        Expr.Logical[] clauses = new Expr.Logical[to.size()];
        for (int i = 0; i != clauses.length; ++i) {
            clauses[i] = constructTypeTest(to.get(i), from, argument, heap, item);
        }
        return OR(clauses, ATTRIBUTE(item));
    }

    private Expr.Logical constructFunctionTypeTest(WyilFile.Type.Function to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        // Ensure lambda argument unboxed
        Expr nArgument = cast(to,from,argument);
        // Construct type test (when necessary)
        return nArgument != argument ? INVOKE("Lambda#is", argument, ATTRIBUTE(item)) : CONST(true);
    }

    private Expr.Logical constructMethodTypeTest(WyilFile.Type.Method to, WyilFile.Type from, Expr argument, Expr heap, SyntacticItem item) {
        // Ensure lambda argument unboxed
        Expr nArgument = cast(to,from,argument);
        // Construct type test (when necessary)
        return nArgument != argument ? INVOKE("Lambda#is", argument, ATTRIBUTE(item)) : CONST(true);
    }

    // ==============================================================================
    // Type Coercions
    // ==============================================================================

    /**
     * <p>
     * Box or Unbox a given type as necessary. For example. consider the following:
     * </p>
     *
     * <pre>
     * int|null x= 1
     * </pre>
     *
     * <p>
     * On the right-hand side we have an (unboxed) value of Boogie type
     * <code>int</code>, but the left-hand side has (boxed) type <code>Value</code>.
     * Hence, we have to call <code>Int#box(1)</code> to box the right-hand side.
     * </p>
     *
     * <p>
     * The key difference between this method and <code>box()</code> and
     * <code>unbox()</code> is that, when calling this method, we don't know which
     * direction the boxing should occur.
     * </p>
     *
     * @param to
     * @param from
     * @param e
     * @return
     */
    private static Expr cast(WyilFile.Type to, WyilFile.Type from, Expr e) {
        // Determine boxed status of each
        boolean t = isBoxed(to);
        boolean f = isBoxed(from);
        // box/unbox as necessary
        if (t && !f) {
            return box(from, e);
        } else if (!t && f) {
            return unbox(to, e);
        } else {
            return e;
        }
    }

    /**
     * Box/unbox zero or more expressions as necessary based on their current type, and their target type.
     *
     * @param target
     * @param from
     * @param args
     * @return
     */
    private static List<Expr> cast(WyilFile.Type target, Tuple<WyilFile.Expr> from, List<Expr> args) {
        ArrayList<Expr> es = new ArrayList<>();
        for (int i = 0; i != args.size(); ++i) {
            es.add(cast(target.dimension(i), from.get(i).getType(), args.get(i)));
        }
        return es;
    }


    /**
     * Determine whether the Boogie representation of a given Whiley type is naturally boxed or not. Boxed types are
     * whose represented by `Value`. However, some Whiley types (e.g. `int`) can be represented directly in Boogie and,
     * hence, are done so.
     *
     * @param type
     * @return
     */
    private static boolean isBoxed(WyilFile.Type type) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_null:
            case WyilFile.TYPE_any:
            case WyilFile.TYPE_universal:
            case WyilFile.TYPE_union:
                return true;
            case WyilFile.TYPE_nominal: {
                WyilFile.Type.Nominal n = (WyilFile.Type.Nominal) type;
                // FIXME: problem with recursive types?
                return isBoxed(n.getConcreteType());
            }
        }
        return false;
    }

    /**
     * Box a given expression into a <code>WVal</code> as necessary. This is used in situations where a given expression
     * must have type <code>WVal</code> but, at the given point, may be still unboxed.
     *
     * @param type The type the expression is being boxed from.
     * @param expr The expression being boxed.
     * @return
     */
    private static Expr box(WyilFile.Type type, Expr expr) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_bool:
                return coerce(expr, "Bool#unbox", "Bool#box");
            case WyilFile.TYPE_byte:
                return coerce(expr, "Byte#unbox", "Byte#box");
            case WyilFile.TYPE_int:
                return coerce(expr, "Int#unbox", "Int#box");
            case WyilFile.TYPE_record:
                return coerce(expr, "Record#unbox", "Record#box");
            case WyilFile.TYPE_reference:
                return coerce(expr, "Ref#unbox", "Ref#box");
            case WyilFile.TYPE_property:
            case WyilFile.TYPE_function:
            case WyilFile.TYPE_method:
                return coerce(expr, "Lambda#unbox", "Lambda#box");
            case WyilFile.TYPE_array:
                return coerce(expr, "Array#unbox", "Array#box");
            case WyilFile.TYPE_nominal: {
                WyilFile.Type.Nominal t = (WyilFile.Type.Nominal) type;
                // Decision on whether boxing required depends on underlying type!
                return box(t.getConcreteType(), expr);
            }
        }
        return expr;
    }

    /**
     * Box zero or more argument values (using the main box function above).
     *
     * @param type  The target type whose shape is expected to match the number of expressions being boxed.
     * @param exprs The list of expressions to be boxed.
     * @return
     */
    private static List<Expr> box(WyilFile.Type type, List<Expr> exprs) {
        ArrayList<Expr> rs = new ArrayList<>();
        for (int i = 0; i != exprs.size(); ++i) {
            rs.add(box(type.dimension(i), exprs.get(i)));
        }
        return rs;
    }

    /**
     * Unbox a given expression into a <code>WVal</code> as necessary. This is required, for example, when primitive
     * values are moving into general dictionaries.
     *
     * @param type
     * @param e
     * @return
     */
    private static Expr unbox(WyilFile.Type type, Expr e) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_bool:
                return coerce(e, "Bool#box", "Bool#unbox");
            case WyilFile.TYPE_byte:
                return coerce(e, "Byte#box", "Byte#unbox");
            case WyilFile.TYPE_int:
                return coerce(e, "Int#box", "Int#unbox");
            case WyilFile.TYPE_record:
                return coerce(e, "Record#box", "Record#unbox");
            case WyilFile.TYPE_reference:
                return coerce(e, "Ref#box", "Ref#unbox");
            case WyilFile.TYPE_property:
            case WyilFile.TYPE_function:
            case WyilFile.TYPE_method:
                return coerce(e, "Lambda#box", "Lambda#unbox");
            case WyilFile.TYPE_array:
                return coerce(e, "Array#box", "Array#unbox");
            case WyilFile.TYPE_nominal: {
                WyilFile.Type.Nominal t = (WyilFile.Type.Nominal) type;
                // Decision on whether boxing required depends on underlying type!
                return unbox(t.getConcreteType(), e);
            }
        }
        return e;
    }

    /**
     * Unbox a given expression on demand based on its structure.
     * @param type
     * @param e
     * @return
     */
    public static Expr unboxAsNecessary(WyilFile.Type type, Expr e) {
        if(e instanceof Expr.DictionaryAccess) {
            return unbox(type,e);
        } else {
            return e;
        }
    }

    /**
     * Convert a given expression using two coercion functions (to and from). This performs some simple optimisations to
     * eliminate chained coercions (e.g.
     * <code>box(unbox(x))</code> becomes <code>x</code>).
     *
     * @param e
     * @return
     */
    private static Expr coerce(Expr e, String from, String to) {
        if (e instanceof Expr.Invoke) {
            Expr.Invoke i = (Expr.Invoke) e;
            if (i.getName().equals(from)) {
                return i.getArguments().get(0);
            }
        }
        // NOTE: we need to pass through the attributes from the expression coerced, otherwise there will be problems with error reporting.
        return INVOKE(to, e, e.getAttributes());
    }

    // ==============================================================================
    // Framing
    // ==============================================================================

    /**
     * Construct a logical test to see whether a given reference (<code>p</code>) is within the "cone" of another
     * variable (<code>q</code>).  For example, consider this:
     * <pre>
     * type List is null | &{ List next, int data }
     *
     * method reverse(List l) -> (List r):
     *    ...
     * </pre>
     *
     * In this case, the cone of <code>l</code> is all those nodes which are reachable from it.  They key to framing,
     * for example, that nodes outside of this cone are unaffected by this method.
     *
     * @param type
     * @param p
     * @param q
     * @param heap
     * @param item
     * @return
     */
    private Expr.Logical within(WyilFile.Type type, Expr p, Expr q, Expr heap, SyntacticItem item) {
        if(WyilUtils.isPure(type)) {
            // handle general case
            return CONST(false, ATTRIBUTE(type));
        } else {
            switch (type.getOpcode()) {
                case WyilFile.TYPE_method:
                    return CONST(false, ATTRIBUTE(type));
                case WyilFile.TYPE_reference:
                    return INVOKE("Ref#within", heap, p, q, ATTRIBUTE(item));
                case WyilFile.TYPE_array:
                    return INVOKE("Array#within", heap, p, q, ATTRIBUTE(item));
                case WyilFile.TYPE_record:
                    return INVOKE("Record#within", heap, p, q, ATTRIBUTE(item));
                case WyilFile.TYPE_union:
                    return INVOKE("Any#within", heap, p, q, ATTRIBUTE(item));
                case WyilFile.TYPE_nominal: {
                    WyilFile.Type.Nominal t = (WyilFile.Type.Nominal) type;
                    return within(t.getConcreteType(), p, q, heap, item);
                }
                default:
                    throw new IllegalArgumentException("unknown type encoutnered (" + type.getClass().getName() + ")");
            }
        }
    }

    private Expr.Logical within(Expr r, Tuple<WyilFile.Decl.Variable> variables, Expr heap, SyntacticItem item) {
        ArrayList<Expr.Logical> clauses = new ArrayList();
        for(int i=0;i!=variables.size();++i) {
            WyilFile.Decl.Variable ith = variables.get(i);
            clauses.add(within(ith.getType(), r, VAR(toVariableName(ith)), heap, item));
        }
        return OR(clauses);
    }

    private Expr.Logical within(WyilFile.Type type, Expr r, Function<Integer,String> parameters, Expr heap, SyntacticItem item) {
        ArrayList<Expr.Logical> clauses = new ArrayList();
        for(int i=0;i!=type.shape();++i) {
            clauses.add(within(type.dimension(i), r, VAR(parameters.apply(i)), heap, item));
        }
        return OR(clauses);
    }

    // ==============================================================================
    // Method Framing
    // ==============================================================================

    /**
     * <p>Construct the dynamic frame representing all references reachable from a given set of root variables.  For
     * example, consider the following:</p>
     * <pre>
     *    method m(&int x) -> (int r):
     *      ...
     * </pre>
     * <p>In this case, the dynamic frame consists of exactly one reference: <code>x</code>.  The purpose of determining
     * the dynamic frame is that this allows us to implicitly scope any locations which could be modified by a given
     * method.</p>
     *
     * @param variables
     * @return
     */
    private List<Expr.Logical> constructMethodFrame(WyilFile.Decl.Method m) {
        Tuple<WyilFile.Decl.Variable> params = m.getParameters();
        Tuple<WyilFile.Decl.Variable> rets = m.getReturns();
        return constructMethodFrame(m.getType(), i -> toVariableName(params.get(i)), i -> toVariableName(rets.get(i)), m);
    }

    private List<Expr.Logical> constructMethodFrame(WyilFile.Type.Callable ct, Function<Integer,String> parameters, Function<Integer,String> returns, SyntacticItem item) {
        ArrayList<Expr.Logical> ensures = new ArrayList<>();
        WyilFile.Type param = ct.getParameter();
        WyilFile.Type ret = ct.getReturn();
        Expr p = VAR("p");
        Expr q = VAR("q");
        // Extract the set of locations reachable from parameter types to this method
        Expr.Logical preParamFrame_p = within(param, p, parameters, OLD_HEAP, item);
        Expr.Logical preParamFrame_q = within(param, q, parameters, OLD_HEAP, item);
        Expr.Logical postRetFrame_p = within(ret, p, returns, HEAP, item);
        Expr.Logical postFrame_p = OR(within(param, p, parameters, HEAP, item),postRetFrame_p);
        // Ensure type invariants guaranteed
        ArrayList<Expr.Logical> inclusions = new ArrayList<>();
        //
        for(int i=0;i!=param.shape();++i) {
            inclusions.add(constructTypeTest(param.dimension(i), VAR(parameters.apply(i)), HEAP, item));
        }
        for(int i=0;i!=ret.shape();++i) {
            inclusions.add(constructTypeTest(ret.dimension(i), VAR(returns.apply(i)), HEAP, item));
        }
        // Add type tests for parameters and returns
        ensures.add(AND(inclusions));
        // NOTE: guards against bits being true/false are necessary to prevent infinite loops it seems.
        if(!preParamFrame_p.isTrue()) {
            // For any reference not in the preframe, either it was unnallocated or its contents are unchanged.
            ensures.add(FORALL("p", REF, OR(preParamFrame_p, EQ(GET(OLD_HEAP, p), VOID), EQ(GET(OLD_HEAP, p), GET(HEAP, p)))));
            if(!postRetFrame_p.isFalse()) {
                // For any reference in the (returned) postframe, either it existed in the preframe or it was unallocated.
                ensures.add(FORALL("p", REF, OR(NOT(postRetFrame_p), EQ(GET(OLD_HEAP, p), VOID), preParamFrame_p)));
            }
        }
        if(!preParamFrame_p.isTrue() && !postFrame_p.isFalse()) {
            // Everything was either reachable from the preframe or is unreachable from the postframe (or was unallocated)
            ensures.add(FORALL("p", REF, OR(EQ(GET(OLD_HEAP, p), VOID), preParamFrame_p, NOT(postFrame_p))));
        }
        //
        return ensures;
    }

    // ==============================================================================
    // Loop Framing
    // ==============================================================================

    /**
     * Construct a loop frame for a given loop assume a heap which holds before the loop begins, and a current heap.
     *
     * @param stmt
     * @param OHEAP Heap which holds before loop
     * @param HEAP  Heap which currently holds
     * @return
     */
    private List<Expr.Logical> constructLoopFrame(WyilFile.Stmt.Loop stmt, Expr.VariableAccess OHEAP, Expr.VariableAccess HEAP) {
        ArrayList<Expr.Logical> frame = new ArrayList<>();
        // Determine set of used variables within loop body
        Tuple<WyilFile.Decl.Variable> fvs = extractUsedReferences(stmt.getBody());
        Expr r = VAR("r");
        // Extract the set of locations reachable from parameter types to this method
        //Expr.Logical used = constructDynamicFrame(fvs, r, OHEAP, stmt);
        Expr.Logical used = within(r, fvs, OHEAP, stmt);
        // For any reference not used in the loop, either it was unnallocated or its contents are unchanged.
        frame.add(FORALL("r", REF, OR(used, EQ(GET(OHEAP, r), VOID), EQ(GET(OHEAP, r), GET(HEAP, r)))));
        // Add additional type constraints for modified references
        frame.addAll(0, constructTypeConstraints(fvs, HEAP));
        // Done
        return frame;
    }

    private Tuple<WyilFile.Decl.Variable> extractUsedReferences(WyilFile.Stmt root) {
        HashSet<WyilFile.Decl.Variable> used = new HashSet<>();
        HashSet<WyilFile.Decl.Variable> declared = new HashSet<>();
        //
        new AbstractVisitor(meter) {
            @Override
            public void visitVariable(WyilFile.Decl.Variable e) {
                declared.add(e);
            }
            @Override
			public void visitVariableAccess(WyilFile.Expr.VariableAccess e) {
                WyilFile.Decl.Variable v = e.getVariableDeclaration();
                if(!declared.contains(v) && !WyilUtils.isPure(v.getType())) {
                    used.add(v);
                }
            }

            @Override
			public void visitLVals(Tuple<WyilFile.LVal> lvs) {
                for(WyilFile.LVal lv : lvs) {
                    visitLVal(lv);
                }
            }

            private void visitLVal(WyilFile.LVal lv) {
                switch(lv.getOpcode()) {
                    case WyilFile.EXPR_variablecopy:
                    case WyilFile.EXPR_variablemove:
                        // Do nothing
                        break;
                    case WyilFile.EXPR_arrayaccess: {
                        WyilFile.Expr.ArrayAccess e = (WyilFile.Expr.ArrayAccess) lv;
                        visitLVal((WyilFile.LVal) e.getFirstOperand());
                        visitExpression(e.getSecondOperand());
                        break;
                    }
                    case WyilFile.EXPR_recordaccess: {
                        WyilFile.Expr.RecordAccess e = (WyilFile.Expr.RecordAccess) lv;
                        visitLVal((WyilFile.LVal) e.getOperand());
                        break;
                    }
                    case WyilFile.EXPR_dereference:
                    case WyilFile.EXPR_fielddereference: {
                        visitExpression(lv);
                        break;
                    }
                }
            }
        }.visitStatement(root);
        //
        return new Tuple<>(used);
    }

    private static WyilFile.Decl.Variable extractDefinedVariable(WyilFile.LVal lval) {
        switch (lval.getOpcode()) {
            case WyilFile.EXPR_arrayaccess:
            case WyilFile.EXPR_arrayborrow: {
                WyilFile.Expr.ArrayAccess e = (WyilFile.Expr.ArrayAccess) lval;
                return extractDefinedVariable((WyilFile.LVal) e.getFirstOperand());
            }
            case WyilFile.EXPR_fielddereference: {
                WyilFile.Expr.FieldDereference e = (WyilFile.Expr.FieldDereference) lval;
                return extractDefinedVariable((WyilFile.LVal) e.getOperand());
            }
            case WyilFile.EXPR_dereference: {
                WyilFile.Expr.Dereference e = (WyilFile.Expr.Dereference) lval;
                return extractDefinedVariable((WyilFile.LVal) e.getOperand());
            }
            case WyilFile.EXPR_recordaccess:
            case WyilFile.EXPR_recordborrow: {
                WyilFile.Expr.RecordAccess e = (WyilFile.Expr.RecordAccess) lval;
                return extractDefinedVariable((WyilFile.LVal) e.getOperand());
            }
            case WyilFile.EXPR_variablecopy:
            case WyilFile.EXPR_variablemove: {
                WyilFile.Expr.VariableAccess e = (WyilFile.Expr.VariableAccess) lval;
                return e.getVariableDeclaration();
            }
            default:
                throw new IllegalArgumentException("invalid lval: " + lval);
        }
    }
    // ==============================================================================
    // Misc
    // ==============================================================================

    private static List<Expr> toArguments(List<Decl.Parameter> params) {
        List<Expr> args = new ArrayList<>();
        // Add remaining arguments
        for (int i = 0; i != params.size(); ++i) {
            args.add(VAR(params.get(i).getName()));
        }
        return args;
    }

    private static List<Expr> toPostArguments(String name, List<Expr> args, List<Decl.Parameter> returns) {
        ArrayList<Expr> postArgs = new ArrayList<>();
        if (returns.size() == 1) {
            postArgs.add(INVOKE(name, args));
        } else {
            // Functions with multiple returns require special handling
            for (int i = 0; i != returns.size(); ++i) {
                postArgs.add(INVOKE(name + "#" + i, args));
            }
        }
        return postArgs;
    }

    private Expr constructMetaType(WyilFile.Type type, Expr heap) {
        String name = "Type#" + getMangle(type);
        Tuple<WyilFile.Template.Variable> holes = WyilUtils.extractTemplate(type,meter);
        if(type instanceof WyilFile.Type.Universal) {
            WyilFile.Type.Universal ut = (WyilFile.Type.Universal) type;
            return VAR(ut.getOperand().get());
        } else if(holes.size() == 0) {
            return VAR(name);
        } else {
            ArrayList<Expr> args = new ArrayList<>();
            for(WyilFile.Template.Variable hole : holes) {
                args.add(VAR(hole.getName().get()));
            }
            return INVOKE(name,args);
        }
    }

    private String toLambdaMangle(WyilFile.Type.Callable ft) {
        String mangle = getMangle(ft);
        if(ft instanceof WyilFile.Type.Method) {
            return "m_apply$" + mangle;
        } else {
            return "f_apply$" + mangle;
        }
    }

    private String getMangle(WyilFile.Type type) {
        if(type == WyilFile.Type.Void) {
            return "V";
        } else {
            return mangler.getMangle(type);
        }
    }

    private String toVariableName(WyilFile.Decl.Variable v) {
        if (mangling) {
            return v.getName().get() + "$" + v.getIndex();
        } else {
            return v.getName().get();
        }
    }

    /**
     * Check whether a given (loop) statement contains a break or continue (which is not contained within another).
     * Observer that only the outermost loop counts, and we should terminate the search for any inner loops. To do this,
     * we use a simple visitor over the abstract tree.
     *
     * @param s
     * @param isBreak
     * @return
     */
    private boolean containsContinueOrBreak(WyilFile.Stmt s, boolean isBreak) {
        //
        return new AbstractVisitor(meter) {
            public boolean result = false;

            public boolean run() {
                super.visitStatement(s);
                return result;
            }

            @Override
            public void visitBreak(WyilFile.Stmt.Break stmt) {
                if (isBreak) {
                    result = true;
                }
            }

            @Override
            public void visitContinue(WyilFile.Stmt.Continue stmt) {
                if (!isBreak) {
                    result = true;
                }
            }

            @Override
            public void visitDoWhile(WyilFile.Stmt.DoWhile stmt) {
                if (stmt != s) {
                    return;
                } else {
                    super.visitDoWhile(stmt);
                }
            }

            @Override
            public void visitFor(WyilFile.Stmt.For stmt) {
                if (stmt != s) {
                    return;
                } else {
                    super.visitFor(stmt);
                }
            }

            @Override
            public void visitLambda(WyilFile.Decl.Lambda stmt) {
                if (stmt != s) {
                    return;
                } else {
                    super.visitLambda(stmt);
                }
            }

            @Override
            public void visitWhile(WyilFile.Stmt.While stmt) {
                if (stmt != s) {
                    return;
                } else {
                    super.visitWhile(stmt);
                }
            }
        }.run();
    }

    /**
     * Find the enclosing loop of a given statement. This could be deprecated in the future using a better query
     * mechanism for ASTs in <code>WyilFile</code>.
     *
     * @param stmt
     * @return
     */
    private static WyilFile.Stmt getEnclosingLoop(WyilFile.Stmt stmt) {
        if (stmt == null) {
            throw new IllegalArgumentException("no enclosing loop found");
        } else if (stmt instanceof WyilFile.Stmt.Loop || stmt instanceof WyilFile.Stmt.For) {
            return stmt;
        } else {
            return getEnclosingLoop(stmt.getParent(WyilFile.Stmt.class));
        }
    }

    /**
     * Check whether a given variable is marked as final or not. This is useful to avoid shadow variables in some case.
     *
     * @param var
     * @return
     */
    public static boolean isFinal(WyilFile.Decl.Variable var) {
        return var.getModifiers().match(WyilFile.Modifier.Final.class) != null;
    }

    /**
     * Check whether a given method declaration ends in a return statement or not. If it doesn't then we need to insert
     * a final assignment of the heap variable
     *
     * @param var
     * @return
     */
    public static boolean hasFinalReturn(WyilFile.Decl.FunctionOrMethod m) {
        WyilFile.Stmt.Block b = m.getBody();
        if (b != null && b.size() > 0) {
            WyilFile.Stmt s = b.get(b.size() - 1);
            return s instanceof WyilFile.Stmt.Return;
        }
        return false;
    }

    /**
     * Determine the set of all field names used within a given WyilFile. This is necessary as we must enumerate field
     * names in order to use them. To achieve this, we recurse the AST looking for all record types.
     *
     * @param wf
     * @return
     */
    private Set<String> determineFieldNames(WyilFile wf) {
        Set<String> names = new HashSet<>();
        AbstractVisitor visitor = new AbstractVisitor(meter) {
            @Override
            public void visitTypeRecord(WyilFile.Type.Record t) {
                // Continue visiting children
                super.visitTypeRecord(t);
                // Add all field names
                for (WyilFile.Type.Field f : t.getFields()) {
                    names.add(f.getName().get());
                }
            }

            @Override
            public void visitRecordInitialiser(WyilFile.Expr.RecordInitialiser expr) {
                for (WyilFile.Identifier f : expr.getFields()) {
                    names.add(f.get());
                }
            }

            @Override
            public void visitRecordAccess(WyilFile.Expr.RecordAccess expr) {
                names.add(expr.getField().get());
            }

            @Override
            public void visitFieldDereference(WyilFile.Expr.FieldDereference expr) {
                names.add(expr.getField().get());
            }
        };

        for (WyilFile.Decl.Unit unit : wf.getModule().getUnits()) {
            visitor.visitUnit(unit);
        }
        for (WyilFile.Decl.Unit unit : wf.getModule().getExterns()) {
            visitor.visitUnit(unit);
        }
        return names;
    }

    /**
     * Extract the variable on which a (flatterned) lval is operating.  For example, given <code>x.f[0] = 1</code>, the extracted
     * variable would be <code>x</code>.
     */
    private static WyilFile.Decl.Variable extractVariable(WyilFile.LVal lval, Build.Meter meter) {
        // FIXME: this should really be a query over e.g. lval.getDescendant().
        switch (lval.getOpcode()) {
            case WyilFile.EXPR_arrayaccess:
            case WyilFile.EXPR_arrayborrow: {
                WyilFile.Expr.ArrayAccess e = (WyilFile.Expr.ArrayAccess) lval;
                return extractVariable((WyilFile.LVal) e.getFirstOperand(), meter);
            }
            case WyilFile.EXPR_fielddereference: {
                WyilFile.Expr.FieldDereference e = (WyilFile.Expr.FieldDereference) lval;
                return extractVariable((WyilFile.LVal) e.getOperand(), meter);
            }
            case WyilFile.EXPR_dereference: {
                WyilFile.Expr.Dereference e = (WyilFile.Expr.Dereference) lval;
                return extractVariable((WyilFile.LVal) e.getOperand(), meter);
            }
            case WyilFile.EXPR_recordaccess:
            case WyilFile.EXPR_recordborrow: {
                WyilFile.Expr.RecordAccess e = (WyilFile.Expr.RecordAccess) lval;
                return extractVariable((WyilFile.LVal) e.getOperand(), meter);
            }
            case WyilFile.EXPR_variablecopy:
            case WyilFile.EXPR_variablemove: {
                WyilFile.Expr.VariableAccess e = (WyilFile.Expr.VariableAccess) lval;
                return e.getVariableDeclaration();
            }
            default:
                throw new IllegalArgumentException("invalid lval: " + lval);
        }
    }

    /**
     * Determine whether a given statement "is pure" in some sense.  Specifically, whether or not it allocates memory or
     * writes to the heap.
     *
     * @param s
     * @return
     */
    private boolean isPure(WyilFile.Stmt s) {
        // Check for writes to the heap
        boolean pure = new AbstractVisitor(meter) {
            boolean result = true;

            @Override
            public void visitNew(WyilFile.Expr.New e) {
                result = false;
            }

            @Override
            public void visitInvoke(WyilFile.Expr.Invoke e) {
                super.visitInvoke(e);
                if(e.getLink().getTarget() instanceof WyilFile.Decl.Method) {
                    // Method calls affect the heap!
                    result = false;
                }
            }

            @Override
            public void visitIndirectInvoke(WyilFile.Expr.IndirectInvoke e) {
                super.visitIndirectInvoke(e);
                if(e.getSource().getType() instanceof WyilFile.Type.Method) {
                    // Method calls affect the heap!
                    result = false;
                }
            }

            @Override
			public void visitLVals(Tuple<WyilFile.LVal> lvs) {
                for(WyilFile.LVal lv : lvs) {
                    visitLVal(lv);
                }
            }

            private void visitLVal(WyilFile.LVal lv) {
                switch(lv.getOpcode()) {
                    case WyilFile.EXPR_variablecopy:
                    case WyilFile.EXPR_variablemove:
                        break;
                    case WyilFile.EXPR_arrayaccess: {
                        WyilFile.Expr.ArrayAccess e = (WyilFile.Expr.ArrayAccess) lv;
                        visitLVal((WyilFile.LVal) e.getFirstOperand());
                        break;
                    }
                    case WyilFile.EXPR_recordaccess: {
                        WyilFile.Expr.RecordAccess e = (WyilFile.Expr.RecordAccess) lv;
                        visitLVal((WyilFile.LVal) e.getOperand());
                        break;
                    }
                    case WyilFile.EXPR_dereference:
                    case WyilFile.EXPR_fielddereference: {
                        WyilFile.Decl.Variable v = extractDefinedVariable(lv);
                        // Found a dereference on a free variable, hence problem.
                        result = false;
                    }
                }
            }

            public boolean test() {
                visitStatement(s);
                return result;
            }
        }.test();
        // Done
        return pure;
    }

    /**
     * Extract all lambda declarations used within this WyilFile so that they can be converted into standalone
     * functions.
     *
     * @param wf
     * @return
     */
    private List<WyilFile.Decl.Lambda> extractLambdaDeclarations(WyilFile.Decl d) {
        ArrayList<WyilFile.Decl.Lambda> decls = new ArrayList<>();
        //
        new AbstractVisitor(meter) {
            @Override
            public void visitLambda(WyilFile.Decl.Lambda l) {
                super.visitLambda(l);
                decls.add(l);
            }

            @Override
            public void visitType(WyilFile.Type t) {
                // Terminate traversing types
            }

        }.visitDeclaration(d);
        //
        return decls;
    }

    /**
     * Determine the appropriate mangled string for a given named declaration. This is critical to ensuring that
     * overloaded declarations do not clash.
     *
     * @param decl The declaration for which the mangle is being determined
     * @param type The concrete type for the declaration in question (as this may differ from the declared type when
     *             type parameters are included).
     * @return
     */
    private String toMangledName(WyilFile.Decl.Named<?> decl, WyilFile.Type type) {
        // Determine whether this is an exported symbol or not
        boolean exported = decl.getModifiers().match(WyilFile.Modifier.Export.class) != null;
        // Check whether mangling applies
        if(mangling) {
            // Construct base name
            String name = decl.getQualifiedName().toString().replace("::", "$");
            // Add type mangles for non-exported symbols only
            return exported ? name : (name + "$" + mangler.getMangle(type));
        } else {
            return decl.getName().toString();
        }
    }

    /**
     * Provides a default argument based on declaration's declared type.
     *
     * @param decl
     * @return
     */
    private String toMangledName(WyilFile.Decl.Named<?> decl) {
        return toMangledName(decl, decl.getType());
    }

    /**
     * A "fake" tuple constructor. This is used to work around the
     * <code>AbstractTranslator</code> which wants to turn a Wyil expression into a
     * Boogie expression, but there are no tuples in Boogie! In fact, we don't need to implement arbitrary tuples in
     * Boogie as, at this time, tuples in Whiley are quite limited.
     *
     * @author David J. Pearce
     */
    private static class FauxTuple extends BoogieFile.AbstractItem implements BoogieFile.Expr.Logical {
        private final List<Expr> items;

        public FauxTuple(List<Expr> items, Attribute... attributes) {
            super(attributes); this.items = items;
        }

        public List<Expr> getItems() {
            return items;
        }

        public String toString() {
            return items.toString();
        }
    }

    private static List<Decl> constructCommentHeading(String text) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.add(null);
        decls.add(new Decl.LineComment(separator('=', 80)));
        decls.add(new Decl.LineComment(text));
        decls.add(new Decl.LineComment(separator('=', 80)));
        return decls;
    }

    private static List<Decl> constructCommentSubheading(String text) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.add(null);
        decls.add(new Decl.LineComment(text));
        decls.add(new Decl.LineComment(separator('-', 80)));
        return decls;
    }

    private static String separator(char c, int width) {
        String r = "";
        for (int i = 0; i != width; ++i) {
            r = r + c;
        }
        return r;
    }

    /**
     * Construct a temporary variable associated with a given statement or expression.
     *
     * @param s
     * @param id
     * @return
     */
    private static String TEMP(WyilFile.Stmt s) {
        return "t" + s.getIndex();
    }

    /**
     * Construct a temporary variable associated with a given statement or expression using a given identifier to distinguish
     * different temporaries from the same statement.
     *
     * @param s
     * @param id
     * @return
     */
    private static String TEMP(WyilFile.Stmt s, int id) {
        return "t" + s.getIndex() + "#" + id;
    }

    private static int TEMP_COUNTER = 0;

    private static String TEMP(String prefix) {
        return prefix + "#" + (TEMP_COUNTER++);
    }

    private static Expr.VariableAccess EMPTY_HEAPVAR = VAR("Ref#Empty");
    /**
     * The name used to represent the heap variable which is passed into a method.
     */
    private static Expr.VariableAccess HEAP = VAR("HEAP");
    private static Expr OLD_HEAP = OLD(HEAP);
    private static Decl.Variable HEAP_PARAM = new Decl.Variable("HEAP",REFMAP);
    private static Decl.Parameter NHEAP_PARAM = new Decl.Parameter("#HEAP",REFMAP);
    private static Expr.VariableAccess VOID = VAR("Void");
}
