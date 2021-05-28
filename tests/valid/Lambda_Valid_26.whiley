type fptr is function(int)->(int,int)

function apply(fptr f, int x) -> (int r, int w)
ensures (r,w) == f(x):
    //
    return f(x)

function id(int x) -> (int y, int z)
ensures (x == y) && (x == z):
    return x,x

function inc(int x) -> (int y, int z)
ensures (x == y) && (x+1 == z):
    return x,1

public export method test():
    assert apply(&id,1) == (1,1)
    assert apply(&inc,1) == (1,2)
    assert apply(&(int x -> (x,x)),123) == (123,123)
    assert apply(&(int x -> (x,x+1)),123) == (123,124)
    