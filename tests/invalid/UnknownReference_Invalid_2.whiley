type Point is {int x, int y}

method main(&{int x, ...} q):
    // Following not safe ...
    *q = {x:1}

public export method test():
    &Point p = new Point{x:1,y:2}
    main(p)
    // as now p has now y field!
    assume p->y == 2


