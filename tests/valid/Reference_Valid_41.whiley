method m(&(int[]) x)
ensures *x == old(*x):
    // do nout   
    skip

public export method test():
    &(int[]) l = new [0,1]
    &(int[]) k = new [1,2]
    m(k)
    assert (*l) == [0,1]
    assert (*k) == [1,2]
