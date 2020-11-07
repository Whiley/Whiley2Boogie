

type binary is {int op, expr left, expr right}
type expr is int | binary

public export method test() :
    binary e = {op: 1, left: 1, right: 2}
    assert e.op == 1
    assert e.left == 1
    assert e.right == 2
