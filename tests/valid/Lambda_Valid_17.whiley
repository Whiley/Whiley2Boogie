type fn_t is function(int)->(int,int)

public export method test():
    fn_t f = &(int x -> (x,x))
    //
    (int y, int z) = f(1)
    //
    assume y == 1
    assume z == 1