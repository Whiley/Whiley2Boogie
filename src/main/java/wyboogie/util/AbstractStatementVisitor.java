package wyboogie.util;

import static wyboogie.core.BoogieFile.*;

import java.util.ArrayList;
import java.util.List;

public class AbstractStatementVisitor {
    
    public Stmt visitStatement(Stmt s) {
        if(s instanceof Stmt.Assignment) {
            return constructAssignment((Stmt.Assignment) s);
        } else if(s instanceof Stmt.Assert) {
            return constructAssert((Stmt.Assert) s);
        } else if(s instanceof Stmt.Assume) {
            return constructAssume((Stmt.Assume) s);
        } else if(s instanceof Stmt.Call) {
            return constructCall((Stmt.Call)s);
        } else if(s instanceof Stmt.Goto) {
            return constructGoto((Stmt.Goto)s);
        } else if(s instanceof Stmt.Havoc) {
            return constructHavoc((Stmt.Havoc)s);
        } else if(s instanceof Stmt.Label) {
            return constructLabel((Stmt.Label)s);
        } else if(s instanceof Stmt.IfElse) {
            return visitIfElse((Stmt.IfElse)s);
        } else if(s instanceof Stmt.Return) {
            return constructReturn((Stmt.Return)s);
        } else if(s instanceof Stmt.Sequence) {
            return visitSequence((Stmt.Sequence)s);
        } else if(s instanceof Stmt.While) {
            return visitWhile((Stmt.While)s);
        } else {
            throw new IllegalArgumentException("unknown statement encountered (" + s.getClass().getName() + ")");
        }
    }
    protected Stmt visitSequence(Stmt.Sequence s) {
        List<Stmt> oldStmts = s.getAll();
        List<Stmt> newStmts = oldStmts;
        for (int i = 0; i != s.size(); ++i) {
            Stmt o = newStmts.get(i);
            Stmt n = visitStatement(o);
            if (o != n) {
                if (newStmts == oldStmts) {
                    newStmts = new ArrayList<>(oldStmts);
                }
                newStmts.set(i, n);
            }
        }
        return constructSequence(s, newStmts);
    }
    protected Stmt visitIfElse(Stmt.IfElse s) {
        Stmt trueBranch = visitStatement(s.getTrueBranch());
        Stmt falseBranch = s.getFalseBranch();
        if (falseBranch != null) {
            falseBranch = visitStatement(s.getFalseBranch());
        }
        return constructIfElse(s,trueBranch,falseBranch);
    }
    protected Stmt visitWhile(Stmt.While s) {
        Stmt body = visitStatement(s.getBody());
        return constructWhile(s,body);
    }
    protected Stmt constructAssignment(Stmt.Assignment s) {
        return s;
    }
    protected Stmt constructAssert(Stmt.Assert s) {
        return s;
    }
    protected Stmt constructAssume(Stmt.Assume s) {
        return s;
    }
    protected Stmt constructCall(Stmt.Call s) {
        return s;
    }
    protected Stmt constructIfElse(Stmt.IfElse s, Stmt trueBranch, Stmt falseBranch) {
        if (s.getTrueBranch() == trueBranch && s.getFalseBranch() == falseBranch) {
            return s;
        } else {
            return IFELSE(s.getCondition(), trueBranch, falseBranch);
        }
    }
    protected Stmt constructGoto(Stmt.Goto s) {
        return s;
    }
    protected Stmt constructHavoc(Stmt.Havoc s) {
        return s;
    }
    protected Stmt constructLabel(Stmt.Label s) {
        return s;
    }
    protected Stmt constructReturn(Stmt.Return s) {
       return s;
    }
    protected Stmt constructSequence(Stmt.Sequence s, List<Stmt> stmts) {
        if(s.getAll() == stmts) {
            return s;
        } else {
            return SEQUENCE(stmts);
        }
    }

    protected Stmt constructWhile(Stmt.While s, Stmt body) {
        if (s.getBody() == body) {
            return s;
        } else {
            return WHILE(s.getCondition(), s.getInvariant(), body);
        }
    }
}
