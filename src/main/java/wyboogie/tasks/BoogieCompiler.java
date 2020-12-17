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

import static wyboogie.core.BoogieFile.*;

import wyboogie.core.BoogieFile;
import wyboogie.core.BoogieFile.Decl;
import wyboogie.core.BoogieFile.Expr;
import wyboogie.core.BoogieFile.Stmt;
import wyboogie.core.BoogieFile.LVal;
import wyboogie.io.BoogieFilePrinter;
import wyboogie.util.AbstractExpressionProducer;
import wyboogie.util.Formula;
import wybs.lang.Build.Meter;
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

    public BoogieCompiler(Meter meter, BoogieFile target) {
        super(meter, subtyping);
        this.boogieFile = target;
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
        decls.addAll(constructCommentHeading("TYPE: " + decl.getQualifiedName() + " : " + instantiation));
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
        parameters.add(new Decl.Parameter(HEAP_VARNAME, REFMAP));
        Expr inv = AND(invariant);
        decls.add(FUNCTION(name + "#inv", parameters, Type.Bool, inv));
        // Generate test for the type itself
        Expr.Logical test = constructTypeTest(instantiation, WyilFile.Type.Any, VAR(varName), HEAP_VARNAME);
        arguments.add(unbox(var.getType(), VAR(varName)));
        arguments.add(VAR(HEAP_VARNAME));
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
        }
        return new Decl.Sequence(decls);
    }

    @Override
    public Decl constructProperty(WyilFile.Decl.Property d, List clauses) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentHeading("PROPERTY: " + d.getQualifiedName()));
        // Apply name mangling
        String name = toMangledName(d);
        // Construct container for type constraints
        ArrayList<Expr.Logical> constraints = new ArrayList<>();
        //
        List<Decl.Parameter> parameters = constructTemplateParameters(d.getTemplate());
        parameters.addAll(constructParameters(d.getParameters(), constraints, "Ref#Empty"));
        // FIXME: what to do with the type constraints?
        decls.add(FUNCTION(name, parameters, Type.Bool, AND(clauses)));
        return new Decl.Sequence(decls);
    }

    @Override
    public Decl constructFunction(WyilFile.Decl.Function d, List precondition, List postcondition,
                                  Stmt body) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentHeading("FUNCTION: " + d.getQualifiedName() + " : " + d.getType()));
        // Construct prototype which can be called from expressions.
        decls.addAll(constructFunctionPrototypes(d, precondition, postcondition));
        // Add any lambda's used within the function
        decls.addAll(constructLambdas(d));
        // Add implementation (if one exists)
        if(d.getBody().size() > 0) {
            // Apply name mangling
            String name = toMangledName(d);
            List<Decl.Parameter> parameters = constructParameters(d.getParameters(), precondition, "Ref#Empty");
            List<Decl.Parameter> returns = constructParameters(d.getReturns(), postcondition, "Ref#Empty");
            // Construct shadow parameters (if applicable, and before heap variable)
            List<Decl.Parameter> shadows = constructShadowParameters(d.getParameters(), parameters);
            // Determine local variables
            List<Decl.Variable> locals = constructLocals(d.getBody());
            // Add shadown assignments to the body
            body = addShadowAssignments(locals, body, parameters, shadows);
            // Add template parameters
            shadows.addAll(0,constructTemplateParameters(d.getTemplate()));
            parameters.addAll(0,constructTemplateParameters(d.getTemplate()));
            // Construct procedure implementation
            decls.addAll(constructCommentSubheading("Implementation"));
            decls.add(new Decl.Procedure(name + "#impl", parameters, returns, precondition, postcondition, Collections.EMPTY_LIST));
            // Construct implementation which can be checked against its specification.
            decls.add(new Decl.Implementation(name + "#impl", shadows, returns, locals, body));
        }
        // Done
        return new Decl.Sequence(decls);
    }

    @Override
    public Decl constructMethod(WyilFile.Decl.Method d, List precondition, List postcondition, Stmt body) {
        // FIXME: this needs to be completely updated
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentHeading("METHOD: " + d.getQualifiedName() + " : " + d.getType()));
        // Apply name mangling
        String name = toMangledName(d);
        List<Decl.Parameter> parameters = constructParameters(d.getParameters(), precondition, HEAP_VARNAME);
        List<Decl.Parameter> returns = constructParameters(d.getReturns(), postcondition, "#" + HEAP_VARNAME);
        // Construct parameters and arguments for specification helpers
        ArrayList<Decl.Parameter> specParametersAndReturns = new ArrayList<>();
        // Add the obligatory heap parameter
        parameters.add(0, new Decl.Variable(HEAP_VARNAME, REFMAP));
        returns.add(0, new Decl.Variable("#" + HEAP_VARNAME, REFMAP));
        specParametersAndReturns.addAll(parameters);
        // Construct function representation precondition
        decls.add(FUNCTION(name + "#pre", specParametersAndReturns, Type.Bool, AND(precondition)));
        // Construct shadow parameters (if applicable, and before heap variable)
        List<Decl.Parameter> shadows = constructShadowParameters(d.getParameters(), parameters);
        shadows.add(0, new Decl.Variable(HEAP_VARNAME + "#", REFMAP));
        // Determine local variables
        List<Decl.Variable> locals = constructLocals(d.getBody());
        // Add shadown assignments to the body
        body = addShadowAssignments(locals, body, parameters, shadows);
        // Check whether last statement is a return or not.
        if (!hasFinalReturn(d)) {
            // Return the updated program heap (only for methods).
            body = SEQUENCE(body, new Stmt.Assignment(VAR("#" + HEAP_VARNAME), VAR(HEAP_VARNAME)));
        }
        // Construct procedure prototype
        decls.add(new Decl.Procedure(name, parameters, returns, precondition, postcondition, Collections.EMPTY_LIST));
        // Add implementation (if one exists)
        if(d.getBody().size() > 0) {
            // Construct implementation which can be checked against its specification.
            decls.add(new Decl.Implementation(name, shadows, returns, locals, body));
            // Add the "lambda" value
            decls.add(new Decl.Constant(true, name + "#lambda", LAMBDA));
        }
        // Add any lambda's used within the method
        decls.addAll(constructLambdas(d));
        // Done
        return new Decl.Sequence(decls);
    }

    /**
     * Construct the "prototype" for a given function. This is a standalone uninterpreted function which can be called
     * directly from within an expression, rather than via a procedure. Whilst this is not strictly necessary, it does
     * help maintain better coherence between the Whiley code and the generated Boogie.
     *
     * @param d
     * @param name
     * @param parameters
     * @param returns
     * @return
     */
    public List<Decl> constructFunctionPrototypes(WyilFile.Decl.Function d, List<Expr.Logical> precondition, List<Expr.Logical> postcondition) {
        Tuple<WyilFile.Template.Variable> template = d.getTemplate();
        WyilFile.Type.Callable instantiation = d.getType();
        ArrayList<Decl> decls = new ArrayList<>();
        // Determine concrete instantiations of this function / method
        List<Decl.Parameter> parameters = constructTemplateParameters(template);
        parameters.addAll(constructParameters(d.getParameters(), instantiation.getParameter(), precondition, "Ref#Empty"));
        List<Decl.Parameter> returns = constructParameters(d.getReturns(), instantiation.getReturn(), postcondition, "Ref#Empty");
        // Construct parameters and arguments for specification helpers
        ArrayList<Decl.Parameter> parametersAndReturns = new ArrayList<>(parameters);
        String name = toMangledName(d, instantiation);
        // Construct function representation precondition
        decls.addAll(constructCommentSubheading("Precondition Check"));
        decls.add(FUNCTION(name + "#pre", parametersAndReturns, Type.Bool, AND(precondition)));
        parametersAndReturns.addAll(returns);
        // Construct function representation postcondition
        decls.addAll(constructCommentSubheading("Postcondition Check"));
        decls.add(FUNCTION(name + "#post", parametersAndReturns, Type.Bool, AND(postcondition)));
        decls.addAll(constructCommentSubheading("Postcondition Axiom"));
        // Construct axiom linking post-condition with prototype.
        decls.add(constructPostconditionAxiom(d, name, parameters, returns));
        decls.addAll(constructCommentSubheading("Prototype"));
        // Construct prototype which can be called from expressions.
        if (returns.isEmpty()) {
            decls.add(FUNCTION(name, parameters, ANY));
        } else if (returns.size() == 1) {
            Type returnType = returns.get(0).getType();
            decls.add(FUNCTION(name, parameters, returnType));
        } else {
            // Multiple returns require special handling
            for (int i = 0; i != returns.size(); ++i) {
                Type returnType = returns.get(i).getType();
                decls.add(FUNCTION(name + "#" + i, parameters, returnType));
            }
        }
        // Add "lambda" value axioms
        decls.addAll(constructCommentSubheading("Lambda Reference & Axiom"));
        decls.addAll(constructLambdaAxioms(d, instantiation));
        // Done
        return decls;
    }

    private List<Decl> constructLambdaAxioms(WyilFile.Decl.FunctionOrMethod d, WyilFile.Type.Callable instantiation) {
        WyilFile.Type param = d.getType().getParameter();
        WyilFile.Type ret = d.getType().getReturn();
        String name = toMangledName(d, instantiation) + "#lambda";
        return constructLambdaAxioms(name, param, ret, d.getTemplate());
    }

    private List<Decl> constructLambdaAxioms(String name, WyilFile.Type param, WyilFile.Type ret, Tuple<WyilFile.Template.Variable> template) {
        String heap = "Ref#Empty"; // not sure what makes sense for methods?
        final int n = param.shape();
        ArrayList<Decl> decls = new ArrayList<>();
        // Add the lambda value
        decls.add(new Decl.Constant(true, name, LAMBDA));
        // Add axiom(s) for the return values
        Expr[] axioms = new Expr[ret.shape()];
        Expr[] args = new Expr[param.shape() + 2];
        ArrayList<Decl.Parameter> vars = new ArrayList<>();
        args[1] = VAR(name);
        for (int i = 0; i != template.size(); ++i) {
            WyilFile.Template.Variable ith = template.get(i);
            vars.add(new Decl.Parameter(ith.getName().get(), TYPE));
        }
        for (int i = 0; i != n; ++i) {
            args[i+2] = VAR("x" + i);
            vars.add(new Decl.Parameter("x" + i, ANY));
        }
        for (int i = 0; i != axioms.length; ++i) {
            args[0] = CONST(i);
            Expr.Logical ivk = constructTypeTest(ret.dimension(i), WyilFile.Type.Any, INVOKE("f_apply$" + n, args), heap);
            Expr axiom = (n == 0) ? ivk : FORALL(vars, ivk);
            decls.add(new Decl.Axiom(axiom));
        }
        return decls;
    }

    public List<Decl.Parameter> constructTemplateParameters(WyilFile.Tuple<WyilFile.Template.Variable> template) {
        ArrayList<Decl.Parameter> decls = new ArrayList<>();
        for (int i = 0; i != template.size(); ++i) {
            WyilFile.Template.Variable ith = template.get(i);
            decls.add(new Decl.Parameter(ith.getName().get(),TYPE));
        }
        return decls;
    }

    /**
     * Convert a sequence of Wyil parameter declarations into a sequence of Boogie parameter declarations. This requires
     * converting the Wyil type to its corresponding Boogie type.
     *
     * @param parameters.  Whiley parameter / return declarations for conversion.
     * @param constraints. Any constraints generated from parameter types will be added to this list of constraints.
     * @param heap.        Identifies the correct name to use when referring to the heap. This matters as in some
     *                     contexts one must refer to the new heap, and in others to the "old" heap.
     * @return
     */
    public List<Decl.Parameter> constructParameters(WyilFile.Tuple<WyilFile.Decl.Variable> parameters, List<Expr.Logical> constraints, String heap) {
        ArrayList<Decl.Parameter> ps = new ArrayList<>();
        for (int i = 0; i != parameters.size(); ++i) {
            WyilFile.Decl.Variable ith = parameters.get(i);
            ps.add(constructParameter(toVariableName(ith), ith.getType(), constraints, heap));
        }
        return ps;
    }

    public List<Decl.Parameter> constructParameters(WyilFile.Tuple<WyilFile.Decl.Variable> parameters, WyilFile.Type type, List<Expr.Logical> constraints, String heap) {
        ArrayList<Decl.Parameter> ps = new ArrayList<>();
        for (int i = 0; i != parameters.size(); ++i) {
            WyilFile.Decl.Variable ith = parameters.get(i);
            ps.add(constructParameter(toVariableName(ith), type.dimension(i), constraints, heap));
        }
        return ps;
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
    public List<Decl.Parameter> constructAnonymousParameters(String prefix, WyilFile.Type type, List<Expr.Logical> constraints,
                                                             String heap) {
        ArrayList<Decl.Parameter> ps = new ArrayList<>();
        for (int i = 0; i != type.shape(); ++i) {
            ps.add(constructParameter(prefix + "#" + i, type.dimension(i), constraints, heap));
        }
        return ps;
    }

    /**
     * Construct the list of parameters to use in the implementation. This differs from that used in the protype /
     * procedure declaration because it must account for <i>shadows</i>. These arise because Whiley allows parameters to
     * be mutated, where as Boogie does not. To work around this, we have shadow parameters (i.e. with different names)
     * which are then assigned to local variables (which can be modified).
     *
     * @param params
     * @param parameters
     * @return
     */
    public List<Decl.Parameter> constructShadowParameters(WyilFile.Tuple<WyilFile.Decl.Variable> params,
                                                          List<Decl.Parameter> parameters) {
        ArrayList<Decl.Parameter> ps = new ArrayList<>();
        for (int i = 0; i != params.size(); ++i) {
            WyilFile.Decl.Variable ith = params.get(i);
            if (isFinal(ith)) {
                ps.add(parameters.get(i));
            } else {
                Type type = constructType(ith.getType());
                ps.add(new Decl.Parameter(ith.getName().get() + "#", type));
            }
        }
        return ps;
    }

    /**
     * Convert a Wyil parameter declaration into a corresponding Boogie one which, in turn, requires converting their
     * types.
     *
     * @param parameter.   The parameter being converted.
     * @param constraints. Any constraint(s) generated from the parameter type will be added to this list of
     *                     constraints.
     * @return
     */
    public Decl.Parameter constructParameter(String name, WyilFile.Type type, List<Expr.Logical> constraints, String heap) {
        // Construct any constraints arising from the parameter's type
        Expr.Logical constraint = constructTypeConstraint(type, VAR(name), heap);
        //
        if (constraint != null) {
            constraints.add(constraint);
        }
        // Done
        return new Decl.Parameter(name, constructType(type));
    }

    /**
     * Add the list of assignments for the shadow parameters to a given function or method body. Basically, for every
     * shadow parameter, there is one assignment to its corresponding local variable.
     *
     * @param locals
     * @param body
     * @param parameters
     * @param implementation
     * @return
     */
    public Stmt addShadowAssignments(List<Decl.Variable> locals, Stmt body, List<Decl.Parameter> parameters,
                                     List<Decl.Parameter> implementation) {
        // Handle parameter shadows
        ArrayList<Stmt> stmts = new ArrayList<>();
        for (int i = 0; i != implementation.size(); ++i) {
            Decl.Parameter ith = implementation.get(i);
            Decl.Parameter pth = parameters.get(i);
            if (ith != pth) {
                locals.add(new Decl.Variable(pth.getName(), pth.getType()));
                stmts.add(new Stmt.Assignment(VAR(pth.getName()),VAR(ith.getName())));
            }
        }
        stmts.add(body);
        return SEQUENCE(stmts);
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
            }

            @Override
            public void visitDeclaration(WyilFile.Decl d) {
                // Prevent unexpected traverals of declarations.
            }

            @Override
            public void visitNew(WyilFile.Expr.New expr) {
                super.visitNew(expr);
                String name = "l#" + expr.getIndex();
                decls.add(new Decl.Variable(name, REF));
            }

            @Override
            public void visitInvoke(WyilFile.Expr.Invoke expr) {
                super.visitInvoke(expr);
                WyilFile.Decl.Callable ft = expr.getLink().getTarget();
                if (ft instanceof WyilFile.Decl.Method) {
                    WyilFile.Type type = expr.getType();
                    if (type.shape() == 1) {
                        // Construct temporary variable
                        decls.add(new Decl.Variable("m#" + expr.getIndex(), constructType(type)));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            decls.add(new Decl.Variable("m#" + expr.getIndex() + "#" + i,
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
                if (ft instanceof WyilFile.Type.Method) {
                    WyilFile.Type type = expr.getType();
                    if (type.shape() == 1) {
                        // Construct temporary variable
                        decls.add(new Decl.Variable("m#" + expr.getIndex(), ANY));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            decls.add(new Decl.Variable("m#" + expr.getIndex() + "#" + i, ANY));
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
     * Construct the "postcondition axiom" which relates a given function prototype to its postcondition. Without this,
     * when an invocation is made to that prototype, Boogie will not be aware of what the postcondition implies.
     *
     * @param prototype
     * @param parameters
     * @return
     */
    public Decl.Axiom constructPostconditionAxiom(WyilFile.Decl.FunctionOrMethod d, String name,
                                                  List<Decl.Parameter> parameters, List<Decl.Parameter> returns) {
        //
        if (d instanceof WyilFile.Decl.Function && parameters.size() == 0) {
            // Easy case, since we don't even need a quantifier.
            if (returns.size() == 1) {
                return new Decl.Axiom(INVOKE(name + "#post", INVOKE(name)));
            } else {
                ArrayList<Expr> args = new ArrayList<>();
                // Functions with multiple returns require special handling
                for (int i = 0; i != returns.size(); ++i) {
                    args.add(INVOKE(name + "#" + i));
                }
                return new Decl.Axiom(INVOKE(name + "#post", args));
            }
        } else {
            // A universal quantifier is required!
            List<Expr> args = new ArrayList<>();
            // Add heap variable (if applicable)
            if (d instanceof WyilFile.Decl.Method) {
                // Clone parameters list to prevent side-effects
                parameters = new ArrayList<>(parameters);
                // Insert new parameter at the beginning
                parameters.add(0, new Decl.Variable(HEAP_VARNAME, REFMAP));
            }
            // Add remaining arguments
            for (int i = 0; i != parameters.size(); ++i) {
                args.add(VAR(parameters.get(i).getName()));
            }
            ArrayList<Expr> postArgs = new ArrayList<>(args);
            //
            if (returns.size() == 1) {
                postArgs.add(INVOKE(name, args));
            } else {
                // Functions with multiple returns require special handling
                for (int i = 0; i != returns.size(); ++i) {
                    postArgs.add(INVOKE(name + "#" + i, args));
                }
            }
            // Construct the axiom
            return new Decl.Axiom(
                    FORALL(parameters, IMPLIES(INVOKE(name + "#pre", args), INVOKE(name + "#post", postArgs))));
        }
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
        WyilFile.Type.Callable type = l.getType();
        WyilFile.Type returnType = type.getReturn();
        boolean method = (type instanceof WyilFile.Type.Method);
        // Extract variables captured in the lambda
        Set<WyilFile.Decl.Variable> captured = l.getCapturedVariables(meter);
        //
        String name = "lambda#" + l.getIndex();
        ArrayList<Decl> decls = new ArrayList<>();
        ArrayList<Expr.Logical> precondition = new ArrayList<>();
        ArrayList<Expr.Logical> postcondition = new ArrayList<>();
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Extract any necessary local variable declarations
        List<Decl.Variable> locals = constructLocals(l.getBody());
        // Convert explicit parameters
        String heap = method ? HEAP_VARNAME : "Ref#Empty";
        String nheap = method ? "#" + HEAP_VARNAME : "Ref#Empty";
        List<Decl.Parameter> parameters = constructParameters(l.getParameters(), precondition, heap);
        // Convert implicit parameters
        parameters.addAll(constructParameters(new Tuple<>(captured), precondition, heap));
        List<Decl.Parameter> protoParameters = new ArrayList<>(parameters);
        // Will contain convert return parameters
        List<Decl.Parameter> returns = constructAnonymousParameters("r", returnType, postcondition, nheap);
        // Add Heap variable if necessary
        if (method) {
            parameters.add(0, new Decl.Parameter(HEAP_VARNAME + "#", REFMAP));
            protoParameters.add(0, new Decl.Parameter(HEAP_VARNAME, REFMAP));
            returns.add(0, new Decl.Parameter("#" + HEAP_VARNAME, REFMAP));
            locals.add(new Decl.Variable(HEAP_VARNAME, REFMAP));
            stmts.add(new Stmt.Assignment(VAR(HEAP_VARNAME), VAR(HEAP_VARNAME + "#")));
        }
        // Translate lambda body
        Expr body = visitExpression(l.getBody());
        // Add all preconditions arising. If there are any, they will likely fail!
        stmts.addAll(constructAssertions(l.getBody()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(l.getBody()));
        //
        for (int i = 0; i != returns.size(); ++i) {
            Decl.Parameter ith = returns.get(i);
            if (method && i == 0) {
                // Heap variable always first return for methods.
                stmts.add(new Stmt.Assignment(VAR("#" + HEAP_VARNAME), VAR(HEAP_VARNAME)));
            } else {
                // FIXME: broken for multiple returns
                stmts.add(new Stmt.Assignment(VAR(ith.getName()), body));
            }
        }
        // Add lambda implementation
        decls.add(new Decl.Procedure(name, protoParameters, returns, precondition, postcondition,
                Collections.EMPTY_LIST));
        decls.add(new Decl.Implementation(name, parameters, returns, locals, SEQUENCE(stmts)));
        // Add the "lambda" value
        decls.addAll(constructLambdaAxioms(name, type.getParameter(), returnType, new Tuple<>()));
        // Done
        return decls;
    }

    @Override
    public Expr constructLambda(WyilFile.Decl.Lambda decl, Expr body) {
        // Read out its "lambda" value
        return VAR("lambda#" + decl.getIndex());
    }

    @Override
    public Stmt constructAssert(WyilFile.Stmt.Assert stmt, Expr condition) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
        //
        stmts.add(new Stmt.Assert((Expr.Logical) condition));
        // DONE
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructAssign(WyilFile.Stmt.Assign stmt, List<Expr> _, List<Expr> rhs) {
        WyilFile.Decl.Method m = stmt.getAncestor(WyilFile.Decl.Method.class);
        // NOTE: in a functional setting, there is no heap variable in play. Therefore,
        // we provide an empty heap in its place.
        String heap = m != null ? HEAP_VARNAME : "Ref#Empty";
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getLeftHandSide()));
        stmts.addAll(constructAssertions(stmt.getRightHandSide()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getRightHandSide()));
        // First, flatten left-hand side
        List<WyilFile.LVal> lvals = flatternAssignmentLeftHandSide(stmt.getLeftHandSide());
        // Second, flatten right-hand side
        List<Expr> rvals = flatternAssignmentRightHandSide(rhs);
        // Third, coerce right-hand side elements
        rvals = coerceAssignmentRightHandSide(lvals, stmt.getRightHandSide(), rvals);
        // Fourth, determine whether simple assign sufficient (or not)
        if (!WyilUtils.isSimple(stmt) && WyilUtils.hasInterference(stmt, meter)) {
            // Simple assignment is insufficient. Therefore, we need to assign every element
            // on the right-hand side into a temporary variable before (subsequently)
            // assigning it into the corresponding item on the left-hand side.
            for (int i = 0; i != rvals.size(); ++i) {
                // Assign item on rhs into temporary
                stmts.add(ASSIGN(VAR(TEMP(stmt, i)), rvals.get(i)));
                // Setup assignment from temporary to the lhs
                rvals.set(i, VAR(TEMP(stmt, i)));
            }
        }
        // Finally, action assignments and type tests
        for (int i = 0; i != lvals.size(); ++i) {
            WyilFile.LVal ith = lvals.get(i);
            stmts.add(constructAssign(ith, rvals.get(i)));
            Expr.Logical c = constructTypeConstraint(ith.getType(), visitExpression(ith), heap);
            if (c != null) {
                stmts.add(new Stmt.Assert(c));
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
    private List<WyilFile.LVal> flatternAssignmentLeftHandSide(Tuple<WyilFile.LVal> lhs) {
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

    /**
     * Flattern the right-hand side of a given assignment. This is relatively straightforward, though we just need to
     * expand any <code>FauxTuple</code>s that we encounter. For example, the following:
     *
     * <pre>
     * x,(y,z) = 1,f()
     * </pre>
     * <p>
     * The right-hand side above is translated into the following:
     *
     * <pre>
     * x,(y,z) = 1,(f#1(),f#2())
     * </pre>
     * <p>
     * Here, <code>(f#1(),f#2())</code> is a <i>faux tuple</i>.
     *
     * @param rhs
     * @return
     */
    private List<Expr> flatternAssignmentRightHandSide(List<Expr> rhs) {
        ArrayList<Expr> rvals = new ArrayList<>();
        // First, flattern all rvals
        for (int i = 0; i != rhs.size(); ++i) {
            Expr ith = rhs.get(i);
            if (ith instanceof FauxTuple) {
                rvals.addAll(((FauxTuple) ith).getItems());
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
    private Stmt constructAssign(WyilFile.LVal lval, Expr rhs) {
        switch (lval.getOpcode()) {
            case WyilFile.EXPR_arrayaccess:
            case WyilFile.EXPR_arrayborrow: {
                WyilFile.Expr.ArrayAccess l = (WyilFile.Expr.ArrayAccess) lval;
                // Reconstruct source expression
                Expr src = visitExpression(l.getFirstOperand());
                // Reconstruct index expression
                Expr index = visitExpression(l.getSecondOperand());
                // Box the right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                // Done
                return constructAssign((WyilFile.LVal) l.getFirstOperand(), PUT(src, index, rhs));
            }
            case WyilFile.EXPR_dereference: {
                WyilFile.Expr.Dereference r = (WyilFile.Expr.Dereference) lval;
                // Reconstruct source expression
                Expr src = visitExpression(r.getOperand());
                // Box the right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                //
                return new Stmt.Assignment(VAR(HEAP_VARNAME), PUT(VAR(HEAP_VARNAME), src, rhs));
            }
            case WyilFile.EXPR_fielddereference: {
                WyilFile.Expr.FieldDereference r = (WyilFile.Expr.FieldDereference) lval;
                // Extract the source reference type
                WyilFile.Type.Reference refT = r.getOperand().getType().as(WyilFile.Type.Reference.class);
                // Extract the source record type
                WyilFile.Type.Record recT = refT.getElement().as(WyilFile.Type.Record.class);
                // Reconstruct source expression
                Expr src = visitExpression(r.getOperand());
                // Reconstruct index expression
                Expr index = VAR("$" + r.getField());
                // Box the right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                // Make the field assignment
                rhs = PUT(unbox(recT, GET(VAR(HEAP_VARNAME), src)), index, rhs);
                // Box again!
                rhs = box(recT, rhs);
                // Done
                return new Stmt.Assignment(VAR(HEAP_VARNAME), PUT(VAR(HEAP_VARNAME), src, rhs));
            }
            case WyilFile.EXPR_recordaccess:
            case WyilFile.EXPR_recordborrow: {
                WyilFile.Expr.RecordAccess l = (WyilFile.Expr.RecordAccess) lval;
                // Reconstruct source expression
                Expr src = visitExpression(l.getOperand());
                // Reconstruct index expression
                Expr index = VAR("$" + l.getField());
                // Box the right-hand side (as necessary)
                rhs = box(lval.getType(), rhs);
                // Done
                return constructAssign((WyilFile.LVal) l.getOperand(), PUT(src, index, rhs));
            }
            case WyilFile.EXPR_variablecopy:
            case WyilFile.EXPR_variablemove: {
                LVal l = (LVal) constructVariableAccess((WyilFile.Expr.VariableAccess) lval);
                // Done
                return new Stmt.Assignment(l, rhs);
            }
            default:
                throw new UnsupportedOperationException("invalid lval");
        }
    }

    @Override
    public Stmt constructAssume(WyilFile.Stmt.Assume stmt, Expr condition) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
        //
        stmts.add(new Stmt.Assume((Expr.Logical) condition));
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
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getOperand()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getOperand()));
        //
        stmts.add(new Stmt.Assert(CONST(true)));
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructDoWhile(WyilFile.Stmt.DoWhile stmt, Stmt body, Expr condition, List invariant) {
        String heap = determineHeapName(stmt);
        //
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // FIXME: handle preconditions and side-effects from the loop invariant(s).
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
        //
        stmts.add(body);
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(new Stmt.Label("CONTINUE_" + stmt.getIndex()));
        }
        // FIXME: handle preconditions and side-effects for subsequent iterations.
        // Add type constraints arising from modified variables
        invariant.addAll(0, constructTypeConstraints(modified, heap));
        // Add the loop itself
        stmts.add(new Stmt.While(condition, invariant, body));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(new Stmt.Label("BREAK_" + stmt.getIndex()));
        }
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructFail(WyilFile.Stmt.Fail stmt) {
        return new Stmt.Assert(CONST(false));
    }

    @Override
    public Stmt constructFor(WyilFile.Stmt.For stmt, Pair range, List invariant, Stmt body) {
        String heap = determineHeapName(stmt);
        //
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        // Determine name of loop variable
        String name = toVariableName(stmt.getVariable());
        Expr.VariableAccess var = VAR(name);
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        // FIXME: handle preconditions and side-effects from the loop invariant(s).
        stmts.addAll(constructAssertions(stmt.getVariable().getInitialiser()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getVariable().getInitialiser()));
        // Extract loop contents so it can be appended later
        ArrayList<Stmt> loopBody = new ArrayList<>();
        loopBody.add(body);
        // Initialise index variable with first value from range
        stmts.add(new Stmt.Assignment(var, (Expr) range.first()));
        Expr condition = LT(var, (Expr) range.second());
        // Add variable increment for completeness
        loopBody.add(new Stmt.Assignment(var, ADD(var, CONST(1))));
        // UPdate the invariant
        invariant.add(0, AND(LTEQ((Expr) range.first(), var), LTEQ(var, (Expr) range.second())));
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(new Stmt.Label("CONTINUE_" + stmt.getIndex()));
        }
        // Add any type constraints arising
        invariant.addAll(0, constructTypeConstraints(modified, heap));
        // Construct the loop
        stmts.add(new Stmt.While(condition, invariant, SEQUENCE(loopBody)));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(new Stmt.Label("BREAK_" + stmt.getIndex()));
        }
        // FIXME: handle preconditions and side-effects arising from subsequent
        // iterations.
        // Done.
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructIfElse(WyilFile.Stmt.IfElse stmt, Expr condition, Stmt trueBranch, Stmt falseBranch) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
        // Add statement!
        stmts.add(new Stmt.IfElse(condition, trueBranch, falseBranch));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructInitialiser(WyilFile.Stmt.Initialiser stmt, Expr init) {
        String heap = determineHeapName(stmt);
        WyilFile.Tuple<WyilFile.Decl.Variable> vars = stmt.getVariables();
        //
        if (init == null) {
            return SEQUENCE();
        } else {
            ArrayList<Stmt> stmts = new ArrayList<>();
            // Add all preconditions arising.
            stmts.addAll(constructAssertions(stmt.getInitialiser()));
            // Apply any heap allocations arising.
            stmts.addAll(constructSideEffects(stmt.getInitialiser()));
            // Extract list of initialiser expressions
            List<Expr> inits = (init instanceof FauxTuple) ? ((FauxTuple) init).getItems() : Arrays.asList(init);
            // Determine type of initialiser expression
            WyilFile.Type initT = stmt.getInitialiser().getType();
            // Assign to each variable and check constraints
            for (int i = 0; i != vars.size(); ++i) {
                WyilFile.Decl.Variable ith = vars.get(i);
                String name = toVariableName(ith);
                stmts.add(ASSIGN(VAR(name), cast(ith.getType(), initT.dimension(i), inits.get(i))));
                // Add assertion for type constraints (if applicable)
                Expr.Logical c = constructTypeConstraint(ith.getType(), VAR(name), heap);
                if (c != null) {
                    stmts.add(new Stmt.Assert(c));
                }
            }
            // FIXME: need post condition!
            return SEQUENCE(stmts);
        }
    }

    @Override
    public Stmt constructInvokeStmt(WyilFile.Expr.Invoke expr, List<Expr> arguments) {
        WyilFile.Type.Callable ft = expr.getLink().getTarget().getType();
        if (ft instanceof WyilFile.Type.Method) {
            WyilFile.Type.Method mt = (WyilFile.Type.Method) ft;
            WyilFile.Type type = mt.getReturn();
            // Apply name mangling
            String name = toMangledName(expr.getLink().getTarget());
            // Determine lvals. Observe that we have to assign any return values from the
            // procedure called, even if they are never used.
            List<LVal> lvals = new ArrayList<>();
            lvals.add(VAR(HEAP_VARNAME));
            if (type.shape() == 1) {
                lvals.add(VAR("m#" + expr.getIndex()));
            } else {
                for (int i = 0; i != type.shape(); ++i) {
                    lvals.add(VAR("m#" + expr.getIndex() + "#" + i));
                }
            }
            // Recursively (re)construct argument expressions
            // FIXME: add argument preconditions and side-effects?
            List<Expr> args = BoogieCompiler.this.visitExpressions(expr.getOperands());
            // Apply conversions to arguments as necessary
            args = cast(mt.getParameter(), expr.getOperands(), args);
            // Chaing through heap variable
            args.add(0, VAR(HEAP_VARNAME));
            // Done
            return CALL(name, lvals, args);
        } else {
            // NOTE: this case arises when for a function invocation which discards the
            // return value. That doesn't really make sense, and for now we just treat as a
            // "skip".
            return new Stmt.Assert(Expr.Boolean.TRUE);
        }
    }

    @Override
    public Stmt constructIndirectInvokeStmt(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments) {
        throw new UnsupportedOperationException("implement me");
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
            // Extract return values
            List<Expr> rvs = returns.size() == 1 ? Arrays.asList(ret) : ((FauxTuple) ret).getItems();
            // Add all preconditions arising.
            stmts.addAll(constructAssertions(stmt.getReturn()));
            // Apply any heap allocations arising.
            stmts.addAll(constructSideEffects(stmt.getReturn()));
            //
            for (int i = 0; i != rvs.size(); ++i) {
                WyilFile.Decl.Variable ith = returns.get(i);
                String rv = toVariableName(ith);
                // Cast returned value as necessary
                Expr re = cast(ith.getType(), type.dimension(i), rvs.get(i));
                // Done
                stmts.add(new Stmt.Assignment(VAR(rv), re));
            }
        }
        if (enclosing instanceof WyilFile.Decl.Method) {
            // Return the updated program heap (only for methods).
            stmts.add(new Stmt.Assignment(VAR("#" + HEAP_VARNAME), VAR(HEAP_VARNAME)));
        }
        // Add the actual return statement!
        stmts.add(new Stmt.Return());
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructSkip(WyilFile.Stmt.Skip stmt) {
        return new Stmt.Assert(Expr.Boolean.TRUE);
    }

    @Override
    public Stmt constructSwitch(WyilFile.Stmt.Switch stmt, Expr condition, List<Pair<List<Expr>, Stmt>> cases) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
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
                cs.add(EQ(condition, ith_first.get(j)));
                defaultCases.add(NEQ(condition, ith_first.get(j)));
            }
            if (cs.isEmpty()) {
                defaultCase = ith.second();
            } else {
                stmts.add(new Stmt.Label(labels.get(i)));
                stmts.add(new Stmt.Assume(OR(cs)));
                stmts.add(ith.second());
                stmts.add(GOTO(breakLabel));
            }
        }
        // Construct default case
        stmts.add(new Stmt.Label(defaultLabel));
        stmts.add(new Stmt.Assume(AND(defaultCases)));
        if (defaultCase != null) {
            stmts.add(defaultCase);
        }
        stmts.add(GOTO(breakLabel));
        // Add final break label
        stmts.add(new Stmt.Label(breakLabel));
        // Done
        return SEQUENCE(stmts);
    }

    @Override
    public Stmt constructWhile(WyilFile.Stmt.While stmt, Expr condition, List invariant, Stmt body) {
        String heap = determineHeapName(stmt);
        //
        boolean needContinueLabel = containsContinueOrBreak(stmt, false);
        boolean needBreakLabel = containsContinueOrBreak(stmt, true);
        Tuple<WyilFile.Decl.Variable> modified = stmt.getModified();
        ArrayList<Stmt> stmts = new ArrayList<>();
        // Add all preconditions arising.
        // FIXME: handle preconditions and side-effects from the loop invariant(s).
        stmts.addAll(constructAssertions(stmt.getCondition()));
        // Apply any heap allocations arising.
        stmts.addAll(constructSideEffects(stmt.getCondition()));
        // Add continue label (if necessary)
        if (needContinueLabel) {
            stmts.add(new Stmt.Label("CONTINUE_" + stmt.getIndex()));
        }
        // FIXME: handle preconditions and side-effects arising from subsequent
        // iterations.
        // Add type constraints arising from modified variables
        invariant.addAll(0, constructTypeConstraints(modified, heap));
        //
        stmts.add(new Stmt.While(condition, invariant, body));
        // Add break label (if necessary)
        if (needBreakLabel) {
            stmts.add(new Stmt.Label("BREAK_" + stmt.getIndex()));
        }
        return SEQUENCE(stmts);
    }

    /**
     * Extract all heap-related side effects (e.g. heap allocations, method calls, etc). For example, consider the
     * following statement in Whiley:
     *
     * <pre>
     * ...
     * &int p = new 1
     * </pre>
     * <p>
     * This is translated into:
     *
     * <pre>
     * var p : Ref;
     * var l#0 : Ref;
     * ...
     * l#0 = new(1);
     * p = l#0;
     * </pre>
     * <p>
     * This is necessary for several reasons. Firstly, <code>new</code> is a procedure and call only be called by the
     * Boogie "call" expression.
     *
     * @param expr
     * @return
     */
    private List<Stmt> constructSideEffects(WyilFile.Expr expr) {
        ArrayList<Stmt> allocations = new ArrayList<>();
        // Handle local variables
        new AbstractVisitor(meter) {

            @Override
            public void visitLambda(WyilFile.Decl.Lambda decl) {
                // NOTE: we don't extract side-effects from lambda declarations. That's because
                // they are effectively encompassed in their own methods.
            }

            @Override
            public void visitNew(WyilFile.Expr.New expr) {
                super.visitNew(expr);
                String name = "l#" + expr.getIndex();
                // Translate operand
                Expr operand = BoogieCompiler.this.visitExpression(expr.getOperand());
                // Box operand (as necessary)
                operand = box(expr.getOperand().getType(), operand);
                // Construct lvals
                List<LVal> lvals = Arrays.asList(VAR(HEAP_VARNAME), VAR(name));
                // Done
                allocations.add(CALL("Ref#new", lvals, VAR(HEAP_VARNAME), operand));
            }

            @Override
            public void visitInvoke(WyilFile.Expr.Invoke expr) {
                super.visitInvoke(expr);
                WyilFile.Decl.Callable ft = expr.getLink().getTarget();
                if (ft instanceof WyilFile.Decl.Method) {
                    WyilFile.Decl.Method mt = (WyilFile.Decl.Method) ft;
                    WyilFile.Type type = expr.getType();
                    // Construct temporary variable(s)
                    List<LVal> lvals = new ArrayList<>();
                    lvals.add(VAR(HEAP_VARNAME));
                    if (type.shape() == 1) {
                        lvals.add(VAR("m#" + expr.getIndex()));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            lvals.add(VAR("m#" + expr.getIndex() + "#" + i));
                        }
                    }
                    // Apply name mangling
                    String name = toMangledName(expr.getLink().getTarget());
                    // Recursively (re)construct argument expressions
                    List<Expr> args = BoogieCompiler.this.visitExpressions(expr.getOperands());
                    // Apply conversions to arguments as necessary
                    args = cast(mt.getType().getParameter(), expr.getOperands(), args);
                    // Chaing through heap variable
                    args.add(0, VAR(HEAP_VARNAME));
                    // Done
                    allocations.add(CALL(name, lvals, args));
                }
            }

            @Override
            public void visitIndirectInvoke(WyilFile.Expr.IndirectInvoke expr) {
                super.visitIndirectInvoke(expr);
                WyilFile.Type.Callable ft = expr.getSource().getType().as(WyilFile.Type.Callable.class);
                //
                if (ft instanceof WyilFile.Type.Method) {
                    WyilFile.Type type = expr.getType();
                    // Construct temporary variable(s)
                    List<LVal> lvals = new ArrayList<>();
                    lvals.add(VAR(HEAP_VARNAME));
                    if (type.shape() == 1) {
                        lvals.add(VAR("m#" + expr.getIndex()));
                    } else {
                        for (int i = 0; i != type.shape(); ++i) {
                            lvals.add(VAR("m#" + expr.getIndex() + "#" + i));
                        }
                    }
                    // Recursively (re)construct source expression
                    Expr source = BoogieCompiler.this.visitExpression(expr.getSource());
                    // Rec)ursively (re)construct argument expressions
                    List<Expr> args = BoogieCompiler.this.visitExpressions(expr.getArguments());
                    // Apply conversions to arguments as necessary
                    args = box(ft.getParameter(), args);
                    // Chain through heap variable
                    args.add(0, VAR(HEAP_VARNAME));
                    // Add method pointer
                    args.add(1, source);
                    // Determine the methods name
                    String name = "m_apply$" + (args.size() - 2) + "#" + (lvals.size() - 1);
                    // Done
                    allocations.add(CALL(name, lvals, args));
                }
            }

            @Override
            public void visitType(WyilFile.Type t) {
                // Prevent unexpected traverals of types
            }
        }.visitExpression(expr);
        //
        return allocations;
    }

    private List<Stmt> constructSideEffects(Tuple<WyilFile.Expr> expr) {
        ArrayList<Stmt> stmts = new ArrayList<>();
        for (int i = 0; i != expr.size(); ++i) {
            stmts.addAll(constructSideEffects(expr.get(i)));
        }
        return stmts;
    }

    @Override
    public Expr constructArrayAccessLVal(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
        return GET(source, index);
    }

    @Override
    public Expr constructDereferenceLVal(WyilFile.Expr.Dereference expr, Expr operand) {
        return GET(VAR(HEAP_VARNAME), operand);
    }

    @Override
    public Expr constructFieldDereferenceLVal(WyilFile.Expr.FieldDereference expr, Expr operand) {
        // First dereference the pointer.
        Expr deref = GET(VAR(HEAP_VARNAME), operand);
        // Second access the given field.
        return GET(deref, VAR("$" + expr.getField()));
    }

    @Override
    public Expr constructRecordAccessLVal(WyilFile.Expr.RecordAccess expr, Expr source) {
        return GET(source, VAR("$" + expr.getField()));
    }

    @Override
    public Expr constructTupleInitialiserLVal(WyilFile.Expr.TupleInitialiser expr, List<Expr> source) {
        return new FauxTuple(source);
    }

    @Override
    public Expr constructVariableAccessLVal(WyilFile.Expr.VariableAccess expr) {
        return constructVariableAccess(expr);
    }

    @Override
    public Expr constructArrayAccess(WyilFile.Expr.ArrayAccess expr, Expr source, Expr index) {
        return unbox(expr.getType(), GET(source, index));
    }

    @Override
    public Expr constructArrayLength(WyilFile.Expr.ArrayLength expr, Expr source) {
        return INVOKE("Array#Length", source);
    }

    @Override
    public Expr constructArrayGenerator(WyilFile.Expr.ArrayGenerator expr, Expr value, Expr length) {
        WyilFile.Type vt = expr.getFirstOperand().getType();
        WyilFile.Type lt = expr.getSecondOperand().getType();
        return INVOKE("Array#Generator", box(vt, value), cast(WyilFile.Type.Int, lt, length));
    }

    @Override
    public Expr constructArrayInitialiser(WyilFile.Expr.ArrayInitialiser expr, List<Expr> values) {
        WyilFile.Type elementType = expr.getType().as(WyilFile.Type.Array.class).getElement();
        Expr arr = INVOKE("Array#Empty", CONST(values.size()));
        //
        for (int i = 0; i != values.size(); ++i) {
            WyilFile.Type type = expr.getOperands().get(i).getType();
            Expr ith = box(type, values.get(i));
            arr = PUT(arr, CONST(i), ith);
        }
        //
        return arr;
    }

    @Override
    public Expr constructBitwiseComplement(WyilFile.Expr.BitwiseComplement expr, Expr operand) {
        return INVOKE("Byte#Not", operand);
    }

    @Override
    public Expr constructBitwiseAnd(WyilFile.Expr.BitwiseAnd expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#And", e, operands.get(i));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseOr(WyilFile.Expr.BitwiseOr expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#Or", e, operands.get(i));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseXor(WyilFile.Expr.BitwiseXor expr, List<Expr> operands) {
        Expr e = operands.get(0);
        for (int i = 1; i != operands.size(); ++i) {
            e = INVOKE("Byte#Xor", e, operands.get(i));
        }
        return e;
    }

    @Override
    public Expr constructBitwiseShiftLeft(WyilFile.Expr.BitwiseShiftLeft expr, Expr lhs, Expr rhs) {
        return INVOKE("Byte#Shl", lhs, INVOKE("Byte#fromInt", rhs));
    }

    @Override
    public Expr constructBitwiseShiftRight(WyilFile.Expr.BitwiseShiftRight expr, Expr lhs, Expr rhs) {
        return INVOKE("Byte#Shr", lhs, INVOKE("Byte#fromInt", rhs));
    }

    @Override
    public Expr constructCast(WyilFile.Expr.Cast expr, Expr operand) {
        // FIXME: unsure whether this is sufficient.
        return cast(expr.getType(), expr.getOperand().getType(), operand);
    }

    @Override
    public Expr constructConstant(WyilFile.Expr.Constant expr) {
        WyilFile.Value v = expr.getValue();
        switch (v.getOpcode()) {
            case WyilFile.ITEM_null: {
                return VAR("Null");
            }
            case WyilFile.ITEM_bool: {
                boolean b = ((WyilFile.Value.Bool) v).get();
                return CONST(b);
            }
            case WyilFile.ITEM_byte: {
                byte b = ((WyilFile.Value.Byte) v).get();
                return CONST(new byte[]{b});
            }
            case WyilFile.ITEM_int: {
                BigInteger i = ((WyilFile.Value.Int) v).get();
                return CONST(i);
            }
            case WyilFile.ITEM_utf8: {
                byte[] bytes = ((WyilFile.Value.UTF8) v).get();
                Expr arr = INVOKE("Array#Empty", CONST(bytes.length));
                //
                for (int i = 0; i != bytes.length; ++i) {
                    Expr ith = box(WyilFile.Type.Int, CONST(bytes[i]));
                    arr = PUT(arr, CONST(i), ith);
                }
                return arr;
            }
            default:
                throw new IllegalArgumentException("unknown constant encountered (" + expr.getClass().getName() + ")");
        }
    }

    @Override
    public Expr constructDereference(WyilFile.Expr.Dereference expr, Expr operand) {
        return unbox(expr.getType(), GET(VAR(HEAP_VARNAME), operand));
    }

    @Override
    public Expr constructFieldDereference(WyilFile.Expr.FieldDereference expr, Expr operand) {
        Expr field = VAR("$" + expr.getField().get());
        // Extract the source reference type
        WyilFile.Type.Reference refT = expr.getOperand().getType().as(WyilFile.Type.Reference.class);
        // Extract the source record type
        WyilFile.Type.Record recT = refT.getElement().as(WyilFile.Type.Record.class);
        // Reconstruct source expression
        Expr deref = unbox(recT, GET(VAR(HEAP_VARNAME), operand));
        //
        return unbox(expr.getType(), GET(deref, field));
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
                result = i == 0 ? EQ(l, r) : AND(result, EQ(l, r));
            }
            // Done
            return result;
        } else if (boxing) {
            return EQ(box(lhsT, lhs), box(rhsT, rhs));
        } else {
            return EQ(lhs, rhs);
        }
    }

    @Override
    public Expr constructIntegerLessThan(WyilFile.Expr.IntegerLessThan expr, Expr lhs, Expr rhs) {
        return LT(lhs, rhs);
    }

    @Override
    public Expr constructIntegerLessThanOrEqual(WyilFile.Expr.IntegerLessThanOrEqual expr, Expr lhs, Expr rhs) {
        return LTEQ(lhs, rhs);
    }

    @Override
    public Expr constructIntegerGreaterThan(WyilFile.Expr.IntegerGreaterThan expr, Expr lhs, Expr rhs) {
        return GT(lhs, rhs);
    }

    @Override
    public Expr constructIntegerGreaterThanOrEqual(WyilFile.Expr.IntegerGreaterThanOrEqual expr, Expr lhs, Expr rhs) {
        return GTEQ(lhs, rhs);
    }

    @Override
    public Expr constructIntegerNegation(WyilFile.Expr.IntegerNegation expr, Expr operand) {
        return NEG(operand);
    }

    @Override
    public Expr constructIntegerAddition(WyilFile.Expr.IntegerAddition expr, Expr lhs, Expr rhs) {
        return ADD(lhs, rhs);
    }

    @Override
    public Expr constructIntegerSubtraction(WyilFile.Expr.IntegerSubtraction expr, Expr lhs, Expr rhs) {
        return SUB(lhs, rhs);
    }

    @Override
    public Expr constructIntegerMultiplication(WyilFile.Expr.IntegerMultiplication expr, Expr lhs, Expr rhs) {
        return MUL(lhs, rhs);
    }

    @Override
    public Expr constructIntegerDivision(WyilFile.Expr.IntegerDivision expr, Expr lhs, Expr rhs) {
        return IDIV(lhs, rhs);
    }

    @Override
    public Expr constructIntegerRemainder(WyilFile.Expr.IntegerRemainder expr, Expr lhs, Expr rhs) {
        return REM(lhs, rhs);
    }

    @Override
    public Expr constructIs(WyilFile.Expr.Is expr, Expr operand) {
        // Determine enclosing heap name
        String heap = determineHeapName(expr);
        //
        return constructTypeTest(expr.getTestType(), expr.getOperand().getType(), operand, heap);
    }

    @Override
    public Expr constructLogicalAnd(WyilFile.Expr.LogicalAnd expr, List operands) {
        return AND(operands);
    }

    @Override
    public Expr constructLogicalImplication(WyilFile.Expr.LogicalImplication expr, Expr lhs, Expr rhs) {
        return IMPLIES((Expr.Logical) lhs, (Expr.Logical) rhs);
    }

    @Override
    public Expr constructLogicalIff(WyilFile.Expr.LogicalIff expr, Expr lhs, Expr rhs) {
        return IFF((Expr.Logical) lhs, (Expr.Logical) rhs);
    }

    @Override
    public Expr constructLogicalNot(WyilFile.Expr.LogicalNot expr, Expr operand) {
        return NOT((Expr.Logical) operand);
    }

    @Override
    public Expr constructLogicalOr(WyilFile.Expr.LogicalOr expr, List operands) {
        return OR(operands);
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
        return EXISTS(ps, AND(clauses));
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
        clauses.add((Expr.Logical) body);
        return FORALL(ps, IMPLIES(AND(clauses), (Expr.Logical) body));
    }

    @Override
    public Expr constructInvoke(WyilFile.Expr.Invoke expr, List<Expr> arguments) {
        ArrayList<Expr> templateArguments = new ArrayList<>();
        Tuple<WyilFile.Type> binding = expr.getBinding().getArguments();
        // Extract (concrete) type signature
        WyilFile.Type.Callable ft = expr.getLink().getTarget().getType();
        // Extract (concrete) return type
        WyilFile.Type rt = expr.getBinding().getConcreteType().getReturn();
        // Add template arguments
        for(int i=0;i!=binding.size();++i) {
            WyilFile.Type ith = substituteUniversalTypes(binding.get(i));
            templateArguments.add(VAR("Type#" + mangler.getMangle(ith)));
        }
        //
        if (ft instanceof WyilFile.Type.Method) {
            // This is a side-effecting method invocation which would have been translated
            // previously.
            if (rt.shape() == 1) {
                return VAR("m#" + expr.getIndex());
            } else {
                List<Expr> items = new ArrayList<>();
                for (int i = 0; i != rt.shape(); ++i) {
                    items.add(VAR("m#" + expr.getIndex() + "#" + i));
                }
                return new FauxTuple(items);
            }
        } else {
            WyilFile.Type ftrt = ft.getReturn();
            // Apply name mangling
            String name = toMangledName(expr.getLink().getTarget());
            // Apply conversions to arguments as necessary
            arguments = cast(ft.getParameter(), expr.getOperands(), arguments);
            // Add template arguments
            arguments.addAll(0,templateArguments);
            //
            if (rt.shape() == 1) {
                return cast(rt, ftrt, INVOKE(name, arguments));
            } else {
                List<Expr> items = new ArrayList<>();
                for (int i = 0; i != rt.shape(); ++i) {
                    items.add(cast(rt.dimension(i), ftrt.dimension(i), INVOKE(name + "#" + i, arguments)));
                }
                return new FauxTuple(items);
            }
        }
    }

    @Override
    public Expr constructIndirectInvoke(WyilFile.Expr.IndirectInvoke expr, Expr source, List<Expr> arguments) {
        WyilFile.Type.Callable type = expr.getSource().getType().as(WyilFile.Type.Callable.class);
        boolean method = (type instanceof WyilFile.Type.Method);
        if (method) {
            return constructIndirectMethodInvoke(expr.getIndex(), expr.getType(), source, arguments);
        } else {
            return constructIndirectFunctionInvoke((WyilFile.Type.Function) type, expr.getType(), source, arguments);
        }
    }

    private Expr constructIndirectFunctionInvoke(WyilFile.Type.Function type, WyilFile.Type ret, Expr source,
                                                 List<Expr> arguments) {
        String base = "f_apply$";
        ArrayList<Expr> args = new ArrayList<>();
        args.add(CONST(0));
        args.add(source);
        // Box all arguments as this is strictly required
        args.addAll(box(type.getParameter(), arguments));
        // Unbox return since it's always boxed
        if (ret.shape() == 1) {
            return unbox(ret, INVOKE(base + arguments.size(), args));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != ret.shape(); ++i) {
                args.set(0, CONST(i));
                items.add(unbox(ret.dimension(i), INVOKE(base + arguments.size(), args)));
            }
            return new FauxTuple(items);
        }
    }

    private Expr constructIndirectMethodInvoke(int index, WyilFile.Type ret, Expr source, List<Expr> arguments) {
        // This is a side-effecting method invocation which would have been translated
        // previously.
        if (ret.shape() == 1) {
            return unbox(ret, VAR("m#" + index));
        } else {
            List<Expr> items = new ArrayList<>();
            for (int i = 0; i != ret.shape(); ++i) {
                items.add(unbox(ret.dimension(i), VAR("m#" + index + "#" + i)));
            }
            return new FauxTuple(items);
        }
    }

    @Override
    public Expr constructLambdaAccess(WyilFile.Expr.LambdaAccess expr) {
        WyilFile.Decl.Callable c = expr.getLink().getTarget();
        // Determine the mangled name for the function in question
        String name = toMangledName(c);
        // Read out its "lambda" value
        return VAR(name + "#lambda");
    }

    @Override
    public Expr constructNew(WyilFile.Expr.New expr, Expr operand) {
        return VAR("l#" + expr.getIndex());
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
                result = i == 0 ? NEQ(l, r) : OR(result, NEQ(l, r));
            }
            // Done
            return result;
        } else if (boxing) {
            return NEQ(box(lhsT, lhs), box(rhsT, rhs));
        } else {
            return NEQ(lhs, rhs);
        }
    }

    @Override
    public Expr constructRecordAccess(WyilFile.Expr.RecordAccess expr, Expr source) {
        Expr field = VAR("$" + expr.getField().get());
        return unbox(expr.getType(), GET(source, field));
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
            rec = PUT(rec, VAR(field), ith);
        }
        //
        return rec;
    }

    @Override
    public Expr constructTupleInitialiser(WyilFile.Expr.TupleInitialiser expr, List<Expr> operands) {
        // NOTE: at this stage, we won't attempt to support general first-class tuples.
        return new FauxTuple(operands);
    }

    @Override
    public Expr constructStaticVariableAccess(WyilFile.Expr.StaticVariableAccess expr) {
        WyilFile.Type declared = expr.getLink().getTarget().getType();
        WyilFile.Type actual = expr.getType();
        // Apply name mangling
        String name = toMangledName(expr.getLink().getTarget());
        // Done
        return cast(actual, declared, VAR(name));
    }

    @Override
    public Expr constructVariableAccess(WyilFile.Expr.VariableAccess expr) {
        WyilFile.Type declared = expr.getVariableDeclaration().getType();
        WyilFile.Type actual = expr.getType();
        // Determine mangled name of this variable
        String name = toVariableName(expr.getVariableDeclaration());
        //
        return cast(actual, declared, VAR(name));
    }

    // =========================================================================================
    // Preconditions
    // =========================================================================================

    /**
     * Construct assertions to ensure all preconditions for a given expression are met.  For example, consider the
     * following statement:
     *
     * <pre>
     *     assert xs[i] >= 0
     * </pre>
     * In this case, there is an implicit precondition that <code>i >=0 && i < |xs|</code>.  As such, we must generate a
     * boogie assertion before the above statement which ensures this is the case.  A more complex example is the
     * following:
     * <pre>
     *    if(i < |xs| && xs[i] >= 0)
     * </pre>
     * <p>This is more complex because we cannot simply create an assertion that <code>i >= 0 && i < |xs|</code> as
     * before. This is because such an assertion would exist before the conditional and, hence, must additionally take
     * into account the we know <code>i < |xs|</code> from the condition itself.  We need to generate the assertion
     * <code>(i < |xs|) ==> (i >= 0 && i < |xs|)</></code> instead.</p>
     * <p><h2>References</h2>
     * <ol>
     *     <li><b>Formalizing a hierarchical structure of practical mathematical reasoning</b>, Robison and Staples, Journal of Logical and Computation.</li>
     * </ol>
     * </p>
     *
     * @param condition
     * @return
     */
    public List<Stmt> constructAssertions(WyilFile.Expr condition) {

        Expr.Logical precondition = new AbstractExpressionProducer<Expr.Logical>() {
            @Override
            protected Expr.Logical BOTTOM() {
                return Expr.Boolean.TRUE;
            }

            @Override
            protected Expr.Logical join(Expr.Logical lhs, Expr.Logical rhs) {
                return AND(lhs,rhs);
            }

            @Override
            protected Expr.Logical join(List<Expr.Logical> operands) {
                return AND(operands);
            }

            @Override
            public Expr.Logical constructLogicalAnd(WyilFile.Expr.LogicalAnd expr, List<Expr.Logical> operands) {
                // Translate Whiley expressions to form the window.
                List window = BoogieCompiler.this.visitExpressions(expr.getOperands());
                Expr.Logical r = operands.get(0);
                for(int i=1;i<operands.size();++i) {
                    Expr.Logical ith = operands.get(i);
                    r = AND(r, IMPLIES(AND(window.subList(0,i)),ith));
                }
                return r;
            }

            @Override
            public Expr.Logical constructLogicalOr(WyilFile.Expr.LogicalOr expr, List<Expr.Logical> operands) {
                // Translate Whiley expressions to form the window.
                List window = BoogieCompiler.this.visitExpressions(expr.getOperands());
                Expr.Logical r = operands.get(0);
                for(int i=1;i<operands.size();++i) {
                    Expr.Logical ith = operands.get(i);
                    r = AND(r, OR(OR(window.subList(0,i)),ith));
                }
                return r;
            }

            @Override
            public Expr.Logical constructLogicalImplication(WyilFile.Expr.LogicalImplication expr, Expr.Logical left, Expr.Logical right) {
                Expr.Logical window = (Expr.Logical) BoogieCompiler.this.visitExpression(expr.getFirstOperand());
                return AND(left,IMPLIES(window,right));
            }

            @Override
            public Expr.Logical constructUniversalQuantifier(WyilFile.Expr.UniversalQuantifier expr, List<Expr.Logical> operands, Expr.Logical body) {
                return constructQuantifier(expr,operands,body);
            }
            @Override
            public Expr.Logical constructExistentialQuantifier(WyilFile.Expr.ExistentialQuantifier expr, List<Expr.Logical> operands, Expr.Logical body) {
                return constructQuantifier(expr,operands,body);
            }

            private Expr.Logical constructQuantifier(WyilFile.Expr.Quantifier expr, List<Expr.Logical> operands, Expr.Logical body) {
                WyilFile.Tuple<WyilFile.Decl.StaticVariable> params = expr.getParameters();
                List<Decl.Parameter> ps = new ArrayList<>();
                List<Expr.Logical> clauses = new ArrayList<>();
                for (int i = 0; i != params.size(); ++i) {
                    WyilFile.Decl.StaticVariable parameter = params.get(i);
                    WyilFile.Expr.ArrayRange range = (WyilFile.Expr.ArrayRange) parameter.getInitialiser();
                    Expr start = BoogieCompiler.this.visitExpression(range.getFirstOperand());
                    Expr end = BoogieCompiler.this.visitExpression(range.getSecondOperand());
                    String name = toVariableName(params.get(i));
                    ps.add(new Decl.Parameter(name, Type.Int));
                    clauses.add(LTEQ(start, VAR(name)));
                    clauses.add(LT(VAR(name), end));
                }
                return AND(AND(operands), FORALL(ps, IMPLIES(AND(clauses), AND(body))));
            }

            @Override
            public Expr.Logical constructArrayAccess(WyilFile.Expr.ArrayAccess expr, Expr.Logical source, Expr.Logical index) {
                Expr src = BoogieCompiler.this.visitExpression(expr.getFirstOperand());
                Expr i = BoogieCompiler.this.visitExpression(expr.getSecondOperand());
                Expr.Logical precondition = AND(LTEQ(CONST(0), i), LT(i, INVOKE("Array#Length", src)));
                return AND(source,index,precondition);
            }

            @Override
            public Expr.Logical constructIntegerDivision(WyilFile.Expr.IntegerDivision expr, Expr.Logical lhs, Expr.Logical rhs) {
                // Translate right-hand side so can compare against 0
                Expr r = BoogieCompiler.this.visitExpression(expr.getSecondOperand());
                // Construct final constraint
                return AND(lhs,rhs,NEQ(r, CONST(0)));
            }

            @Override
            public Expr.Logical constructInvoke(WyilFile.Expr.Invoke expr, List<Expr.Logical> preconditions) {
                Expr.Logical result = AND(preconditions);
                WyilFile.Decl.Callable c = expr.getLink().getTarget();
                Tuple<WyilFile.Type> binding = expr.getBinding().getArguments();
                // Translate arguments
                List<Expr> args = BoogieCompiler.this.visitExpressions(expr.getOperands());
                // Mangle target name
                String name = toMangledName(c);
                // Coerce argument types (as necessary)
                args = cast(c.getType().getParameter(), expr.getOperands(), args);
                // Add template arguments (as necessary)
                for (int i = 0; i != binding.size(); ++i) {
                    WyilFile.Type ith = substituteUniversalTypes(binding.get(i));
                    args.add(i, VAR("Type#" + mangler.getMangle(ith)));
                }
                //
                if (c instanceof WyilFile.Decl.Function) {
                    result = AND(result, INVOKE(name + "#pre", args));
                } else if (c instanceof WyilFile.Decl.Method) {
                    // FIXME: this is surely broken no?
                    args.add(0, VAR(HEAP_VARNAME));
                    result = AND(result, INVOKE(name + "#pre", args));
                }
                return result;
            }
        }.visitExpression(condition);
        //
        List<Stmt> assertions = new ArrayList<>();
        // FIXME: would be good to tidy this all up by e.g. converting it to CNF.
        assertions.add(new Stmt.Assert(precondition));
        //
        return assertions;
    }

    public List<Stmt> constructAssertions(Tuple<? extends WyilFile.Expr> conditions) {
        ArrayList<Stmt> assertions = new ArrayList<>();
        for(int i=0;i!=conditions.size();++i) {
            assertions.addAll(constructAssertions(conditions.get(i)));
        }
        return assertions;
    }

    // =========================================================================================
    // Type Conversion
    // =========================================================================================

    /**
     * The top-level (boxed) type representing all possible values in Whiley.
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
        // Define the top-level Whiley value which contains all others.
        decls.add(new Decl.TypeSynonym("Any", null));
        // Define the top-level Whiley type which contains all others.
        decls.add(new Decl.TypeSynonym("Type", null));
        // Add void constant
        decls.add(new Decl.Constant(true, "Void", ANY));
        // Add all bool axioms
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

    private List<Decl> constructNullAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Nulls"));
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
        decls.add(new Decl.Axiom(FORALL("b", Type.Bool, NEQ(INVOKE("Bool#box", VAR("b")), VAR("Void")))));
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
        decls.add(new Decl.Axiom(FORALL("i", Type.Int, NEQ(INVOKE("Int#box", VAR("i")), VAR("Void")))));
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
        decls.add(new Decl.Axiom(FORALL("b", Type.BitVector8, NEQ(INVOKE("Byte#box", VAR("b")), VAR("Void")))));
        // Done
        return decls;
    }

    /**
     * Construct axioms relevant to array types.
     *
     * @return
     */
    private List<Decl> constructArrayAxioms(WyilFile wf) {
        // NOTE: we could reduce the amount of boxing / unboxing necessary by generating
        // custom array types for each different array type encountered.
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Arrays"));
        decls.add(FUNCTION("Array#box", INTMAP, ANY));
        decls.add(FUNCTION("Array#unbox", ANY, INTMAP));
        decls.add(FUNCTION("Array#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("a", INTMAP, EQ(INVOKE("Array#box", VAR("a")), VAR("v")))));
        // Establish connection between tbox and unbox
        decls.add(new Decl.Axiom(FORALL("i", INTMAP, EQ(INVOKE("Array#unbox", INVOKE("Array#box", VAR("i"))), VAR("i")))));
        // Establish no connection between arrays and Void
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, NEQ(INVOKE("Array#box", VAR("a")), VAR("Void")))));
        // Array length function
        decls.add(FUNCTION("Array#Length", INTMAP, Type.Int));
        // Enforce array length is non-negative
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, LTEQ(CONST(0), INVOKE("Array#Length", VAR("a"))))));
        // Empty arrays
        decls.add(FUNCTION("Array#Empty", Type.Int, INTMAP));
        decls.add(FUNCTION("Array#Generator", ANY, Type.Int, INTMAP));
        // Ensure that all elements outside array length are void
        decls.add(new Decl.Axiom(
                FORALL("l", Type.Int, "i", Type.Int, OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
                        EQ(GET(INVOKE("Array#Empty", VAR("l")), VAR("i")), VAR("Void"))))));
        // Relate empty array with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "l", Type.Int,
                OR(NEQ(INVOKE("Array#Empty", VAR("l")), VAR("a")), EQ(INVOKE("Array#Length", VAR("a")), VAR("l"))))));
        // Ensure that all elements inside generator length are void
        decls.add(new Decl.Axiom(FORALL("v", ANY, "l", Type.Int, "i", Type.Int, OR(LT(VAR("i"), CONST(0)),
                LTEQ(VAR("l"), VAR("i")), EQ(GET(INVOKE("Array#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("v"))))));
        // Ensure that all elements outside generator length are void
        decls.add(new Decl.Axiom(FORALL("v", ANY, "l", Type.Int, "i", Type.Int,
                OR(AND(LTEQ(CONST(0), VAR("i")), LT(VAR("i"), VAR("l"))),
                        EQ(GET(INVOKE("Array#Generator", VAR("v"), VAR("l")), VAR("i")), VAR("Void"))))));
        // Relate array generator with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "v", ANY, "l", Type.Int,
                OR(NEQ(INVOKE("Array#Generator", VAR("v"), VAR("l")), VAR("a")),
                        EQ(INVOKE("Array#Length", VAR("a")), VAR("l"))))));
        // Relate updated array with its length
        decls.add(new Decl.Axiom(FORALL("a", INTMAP, "i", Type.Int, "v", ANY,
                EQ(INVOKE("Array#Length", VAR("a")), INVOKE("Array#Length", PUT(VAR("a"), VAR("i"), VAR("v")))))));
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
        decls.add(new Decl.Axiom(FORALL("r", FIELDMAP, NEQ(INVOKE("Record#box", VAR("r")), VAR("Void")))));
        // Defines the empty record (i.e. the base from which all other records are
        // constructed).
        decls.add(new Decl.Constant(true, "Record#Empty", FIELDMAP));
        decls.add(new Decl.Axiom(FORALL("f", FIELD, EQ(GET(VAR("Record#Empty"), VAR("f")), VAR("Void")))));
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
        decls.add(new Decl.Axiom(FORALL("r", REF, NEQ(INVOKE("Ref#box", VAR("r")), VAR("Void")))));
        // Construct the allocation procedure
        Expr heap = VAR(HEAP_VARNAME);
        Expr nheap = VAR("#" + HEAP_VARNAME);
        Expr.VariableAccess val = VAR("val");
        Expr.VariableAccess ref = VAR("ref");
        //
        List<Decl.Parameter> parameters = Arrays.asList(new Decl.Parameter(HEAP_VARNAME, REFMAP),
                new Decl.Parameter(val.getVariable(), ANY));
        List<Decl.Parameter> returns = Arrays.asList(new Decl.Parameter("#" + HEAP_VARNAME, REFMAP),
                new Decl.Parameter(ref.getVariable(), REF));
        // FIXME: there are still some problems below related to the Void constant which
        // is not necessarily disjoint with all integer constants, etc.
        List<Expr.Logical> requires = new ArrayList<>();
        List<Expr.Logical> ensures = new ArrayList<>();
        // Heap location at ref equals val
        ensures.add(EQ(GET(nheap, ref), val));
        // Heap location not previously allocated!
        ensures.add(EQ(GET(heap, ref), VAR("Void")));
        // All allocated locations remain as before
        ensures.add(FORALL("r", REF, OR(EQ(ref, VAR("r")), EQ(GET(heap, VAR("r")), GET(nheap, VAR("r"))))));
        //
        decls.add(new Decl.Procedure("Ref#new", parameters, returns, requires, ensures, Collections.EMPTY_LIST));
        // Done
        return decls;
    }

    private List<Decl> constructLambdaAxioms(WyilFile wf) {
        ArrayList<Decl> decls = new ArrayList<>();
        decls.addAll(constructCommentSubheading("Lambdas"));
        decls.add(new Decl.TypeSynonym("Lambda", null));
        decls.add(FUNCTION("Lambda#box", LAMBDA, ANY));
        decls.add(FUNCTION("Lambda#unbox", ANY, LAMBDA));
        decls.add(FUNCTION("Lambda#is", new Decl.Parameter("v", ANY), Type.Bool,
                EXISTS("l", LAMBDA, EQ(INVOKE("Lambda#box", VAR("l")), VAR("v")))));
        // Establish connection between box and unbox
        decls.add(new Decl.Axiom(
                FORALL("l", LAMBDA, EQ(INVOKE("Lambda#unbox", INVOKE("Lambda#box", VAR("l"))), VAR("l")))));
        // Establish no connection between lambdas and Void
        decls.add(new Decl.Axiom(FORALL("l", LAMBDA, NEQ(INVOKE("Lambda#box", VAR("l")), VAR("Void")))));
        // Add f_apply functions
        for (int p = 0; p != 5; ++p) {
            List<Decl.Parameter> params = new ArrayList<>();
            params.add(new Decl.Parameter(null, Type.Int));
            params.add(new Decl.Parameter(null, LAMBDA));
            for (int i = 0; i < p; ++i) {
                params.add(new Decl.Parameter(null, ANY));
            }
            decls.add(FUNCTION("f_apply$" + p, params, ANY));
        }
        // Add m_apply functions
        for (int p = 0; p != 5; ++p) {
            for (int r = 0; r != 3; ++r) {
                List<Decl.Parameter> params = new ArrayList<>();
                params.add(new Decl.Parameter("heap", REFMAP));
                params.add(new Decl.Parameter("l", LAMBDA));
                for (int i = 0; i < p; ++i) {
                    params.add(new Decl.Parameter("p" + i, ANY));
                }
                List<Decl.Parameter> returns = new ArrayList<>();
                returns.add(new Decl.Parameter("#heap", REFMAP));
                for (int i = 0; i < r; ++i) {
                    returns.add(new Decl.Parameter("r" + i, ANY));
                }
                // Add heap for method invocations
                decls.add(PROCEDURE("m_apply$" + p + "#" + r, params, returns));
            }
        }
        // done
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
        decls.add(FUNCTION("Type#is",TYPE,ANY,Type.Bool));
        // Extract all types used in a meta-type position
        Set<WyilFile.Type> types = extractMetaTypes(f);
        //
        for (WyilFile.Type type : types) {
            decls.add(null);
            // Remove any unversal types
            type = substituteUniversalTypes(type);
            // Construct meta constant
            String name = "Type#" + mangler.getMangle(type);
            decls.add(new Decl.Constant(true, name, TYPE));
            // Construct a suitable type test
            Expr.Logical test = constructTypeTest(type, WyilFile.Type.Any, VAR("v"), "Ref#Empty");
            // Assert relationship between constant and type test
            decls.add(new Decl.Axiom(FORALL("v", ANY, IFF(INVOKE("Type#is", VAR(name), VAR("v")), test))));
        }
        return decls;
    }

    private WyilFile.Type substituteUniversalTypes(WyilFile.Type type) {
        return type.substitute(o -> { return WyilFile.Type.Any; }) ;
    }

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
        HashSet<WyilFile.Type> visited = new HashSet<>();
        new AbstractVisitor(meter) {
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
    private Expr.Logical constructTypeConstraint(WyilFile.Type type, Expr expr, String heap) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_null:
            case WyilFile.TYPE_bool:
            case WyilFile.TYPE_byte:
            case WyilFile.TYPE_int:
                // No constraints exist on primitive types.
                return null;
            default:
                // Fall back to primitive test
                return constructTypeTest(type, type, expr, heap);
        }
    }

    /**
     * Construct a sequence of zero or more constraints arising from zero or more variables.
     *
     * @param vars
     * @param heap
     * @return
     */
    private List<Expr.Logical> constructTypeConstraints(Tuple<WyilFile.Decl.Variable> vars, String heap) {
        List<Expr.Logical> constraints = new ArrayList<>();
        for (int i = 0; i != vars.size(); ++i) {
            WyilFile.Decl.Variable ith = vars.get(i);
            Expr.Logical c = constructTypeConstraint(ith.getType(), VAR(toVariableName(ith)), heap);
            if (c != null) {
                constraints.add(0, c);
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
     * The expression <code>x is null</code> will be translated by this function.
     *
     * @param to       The type being tested against.
     * @param from     The argument type
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructTypeTest(WyilFile.Type to, WyilFile.Type from, Expr argument, String heap) {
        switch (to.getOpcode()) {
            case WyilFile.TYPE_any:
                return NEQ(argument, VAR("Void"));
            case WyilFile.TYPE_null:
                return EQ(argument, VAR("Null"));
            case WyilFile.TYPE_bool:
                return INVOKE("Bool#is", box(from, argument));
            case WyilFile.TYPE_byte:
                return INVOKE("Byte#is", box(from, argument));
            case WyilFile.TYPE_int:
                return INVOKE("Int#is", box(from, argument));
            case WyilFile.TYPE_universal: {
                WyilFile.Type.Universal t = (WyilFile.Type.Universal) to;
                return INVOKE("Type#is", VAR(t.getOperand().get()), argument);
            }
            case WyilFile.TYPE_property:
                return INVOKE("Lambda#is", box(from, argument));
            case WyilFile.TYPE_function:
                return constructFunctionTypeTest((WyilFile.Type.Function) to, from, argument, heap);
            case WyilFile.TYPE_method:
                return constructMethodTypeTest((WyilFile.Type.Method) to, from, argument, heap);
            case WyilFile.TYPE_nominal:
                return constructNominalTypeTest((WyilFile.Type.Nominal) to, from, argument, heap);
            case WyilFile.TYPE_array:
                return constructArrayTypeTest((WyilFile.Type.Array) to, from, argument, heap);
            case WyilFile.TYPE_record:
                return constructRecordTypeTest((WyilFile.Type.Record) to, from, argument, heap);
            case WyilFile.TYPE_reference:
                return constructReferenceTypeTest((WyilFile.Type.Reference) to, from, argument, heap);
            case WyilFile.TYPE_union:
                return constructUnionTypeTest((WyilFile.Type.Union) to, from, argument, heap);
            default:
                throw new IllegalArgumentException("unknown type encoutnered (" + to.getClass().getName() + ")");
        }
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
    private Expr.Logical constructNominalTypeTest(WyilFile.Type.Nominal to, WyilFile.Type from, Expr argument, String heap) {
        ArrayList<Expr> arguments = new ArrayList<>();
        // Extract template binding
        Tuple<WyilFile.Type> binding = to.getParameters();
        // Construct appropriate name mangle
        String name = toMangledName(to.getLink().getTarget());
        // Add template parameters (if applicable)
        for (int i = 0; i != binding.size(); ++i) {
            WyilFile.Type t = substituteUniversalTypes(binding.get(i));
            arguments.add(VAR("Type#" + mangler.getMangle(t)));
        }
        // Add remaining parameters
        arguments.add(box(from, argument));
        arguments.add(VAR(heap));
        // Ensure argument is boxed!
        return INVOKE(name + "#is", arguments);
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
    private Expr.Logical constructRecordTypeTest(WyilFile.Type.Record to, WyilFile.Type from, Expr argument, String heap) {
        // NOTE: this method for describing a type test should be deprecated in the
        // future in favour of something based around type tags.
        Tuple<WyilFile.Type.Field> fields = to.getFields();
        Expr.Logical[] clauses = new Expr.Logical[fields.size()];
        // Cast argument to correct (unboxed) type
        argument = cast(to, from, argument);
        // Iterate fields constructing tests for each.
        for (int i = 0; i != clauses.length; ++i) {
            WyilFile.Type.Field f = fields.get(i);
            String field = "$" + f.getName().get();
            clauses[i] = constructTypeTest(f.getType(), WyilFile.Type.Any, GET(argument, VAR(field)), heap);
        }
        // FIXME: Should this restrict permitted fields and ensure Record#is?
        // Done
        return AND(clauses);
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
     * @param argument The argument being tested.
     * @return
     */
    private Expr.Logical constructArrayTypeTest(WyilFile.Type.Array to, WyilFile.Type from, Expr argument, String heap) {
        // NOTE: this method for describing a type test should be deprecated in the
        // future in favour of something based around type tags.
        //
        // Generate temporary index variable (which avoids name clashes). Observe that we cannot use the index in this
        // case, because types are not guaranteed to be part of the heap.  For example, when they are constructed for
        // generic nominal types.
        Expr.VariableAccess i = VAR(TEMP("i"));
        // Cast argument to (unboxed) array type
        argument = cast(to, from, argument);
        // Construct bounds check for index variable
        Expr.Logical lhs = AND(LTEQ(CONST(0), i), LT(i, INVOKE("Array#Length", argument)));
        // Recursively construct type test for element
        Expr.Logical rhs = constructTypeTest(to.getElement(), WyilFile.Type.Any, GET(argument, i), heap);
        // FIXME: Should this restrict permitted fields and ensure Array#is?
        // Done
        return FORALL(i.getVariable(), Type.Int, IMPLIES(lhs, rhs));
    }

    private Expr.Logical constructReferenceTypeTest(WyilFile.Type.Reference to, WyilFile.Type from, Expr argument, String heap) {
        // Cast argument to (unboxed) reference type
        argument = cast(to, from, argument);
        // Dereference argument
        Expr deref = GET(VAR(heap), argument);
        // FIXME: Should this restrict permitted fields and ensure Ref#is?
        // Done
        return constructTypeTest(to.getElement(), WyilFile.Type.Any, deref, heap);
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
    private Expr.Logical constructUnionTypeTest(WyilFile.Type.Union to, WyilFile.Type from, Expr argument, String heap) {
        Expr.Logical[] clauses = new Expr.Logical[to.size()];
        for (int i = 0; i != clauses.length; ++i) {
            clauses[i] = constructTypeTest(to.get(i), from, argument, heap);
        }
        return OR(clauses);
    }

    private Expr.Logical constructMethodTypeTest(WyilFile.Type.Method to, WyilFile.Type from, Expr argument, String heap) {
        throw new IllegalArgumentException();
    }

    private Expr.Logical constructFunctionTypeTest(WyilFile.Type.Function to, WyilFile.Type from, Expr argument, String heap) {
        // Determine number of requirement argtuments
        int n = to.getParameter().shape();
        // Extract Return Type
        WyilFile.Type ret = to.getReturn();
        // Setup arguments for invocation
        Expr[] vs = new Expr[n + 2];
        vs[1] = cast(to, from, argument);
        for (int i = 0; i != n; ++i) {
            vs[i + 2] = VAR("x" + i);
        }
        // setup parameters for quantifier (if required)
        ArrayList<Decl.Parameter> params = new ArrayList<>();
        for (int i = 0; i != n; ++i) {
            params.add(new Decl.Parameter("x" + i, ANY));
        }
        // Construct one clause for each return value
        Expr.Logical[] clauses = new Expr.Logical[ret.shape()];
        for (int i = 0; i != clauses.length; ++i) {
            WyilFile.Type ith = ret.dimension(i);
            vs[0] = CONST(i);
            Expr.Logical clause = constructTypeTest(ith, WyilFile.Type.Any, INVOKE("f_apply$" + n, vs), heap);
            clauses[i] = (n == 0) ? clause : FORALL(params, clause);
        }
        // Done
        return AND(INVOKE("Lambda#is", box(from, argument)), AND(clauses));
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
        return INVOKE(to, e);
    }

    // ==============================================================================
    // Misc
    // ==============================================================================

    private Expr constructMetaType(WyilFile.Type type) {
        switch (type.getOpcode()) {
            case WyilFile.TYPE_null:
                return VAR("Null#type");
            case WyilFile.TYPE_bool:
                return VAR("Bool#type");
            case WyilFile.TYPE_byte:
                return VAR("Byte#type");
            case WyilFile.TYPE_int:
                return VAR("Int#type");
            case WyilFile.TYPE_universal:
                return VAR("Any#type");
            case WyilFile.TYPE_nominal: {
                WyilFile.Type.Nominal n = (WyilFile.Type.Nominal) type;
                String name = toMangledName(n.getLink().getTarget());
                // Sanity check for now
                if (n.getParameters().size() > 0) {
                    throw new IllegalArgumentException("PROBLEM");
                }
                // Done
                return VAR(name + "#type");
            }
            case WyilFile.TYPE_record:
            case WyilFile.TYPE_array:
            case WyilFile.TYPE_reference:
            case WyilFile.TYPE_property:
            case WyilFile.TYPE_function:
            case WyilFile.TYPE_method:
        }
        throw new IllegalArgumentException("unknown type encountered : " + type);
    }

    private static String toVariableName(WyilFile.Decl.Variable v) {
        return v.getName().get() + "$" + v.getIndex();
    }

    /**
     * Determine the appropriate heap name to use in a given context. For example, in a pure functional context we
     * always use the empty heap. In contrast, within a method we will use the heap parameter passed in .
     *
     * @param stmt
     * @return
     */
    private static String determineHeapName(WyilFile.Stmt stmt) {
        WyilFile.Decl.Method m = stmt.getAncestor(WyilFile.Decl.Method.class);
        // NOTE: in a functional setting, there is no heap variable in play. Therefore,
        // we provide an empty heap in its place.
        return m != null ? HEAP_VARNAME : "Ref#Empty";
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
    public static boolean hasFinalReturn(WyilFile.Decl.Method m) {
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
        //
        for (WyilFile.Decl.Unit unit : wf.getModule().getUnits()) {
            //
            new AbstractVisitor(meter) {
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
            }.visitUnit(unit);

        }
        return names;
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
        // Construct base name
        String name = decl.getQualifiedName().toString().replace("::", "$");
        // Add type mangles for non-exported symbols only
        return exported ? name : (name + "$" + mangler.getMangle(type));
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
    private static class FauxTuple implements BoogieFile.Expr {
        private final List<Expr> items;

        public FauxTuple(List<Expr> items) {
            this.items = items;
        }

        public List<Expr> getItems() {
            return items;
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
     * Construct a temporary variable associated with a given statement using a given identifier to distinguish
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

    private static String HEAP_VARNAME = "HEAP";
}
