type List is null|Node
type Node is &{ int data, List next }

variant unchanged(List l)
where (l is Node) ==> (l->data == old(l->data))
where (l is Node) ==> unchanged(l->next)

method m(List l)
ensures unchanged(l):
    skip

public export method test():
    List l1 = null
    List l2 = new {data:1,next:l1}
    List l3 = new {data:2,next:l2}
    //
    m(l1)
    assert l2->data == 1
    assert l2->next == null
    assert l3->data == 2
    assert l3->next == l2
    //
    m(l2)
    assert l2->data == 1
    assert l2->next == null
    assert l3->data == 2
    assert l3->next == l2
    //
    m(l3)
    assert l2->data == 1
    assert l2->next == null
    assert l3->data == 2
    assert l3->next == l2
    