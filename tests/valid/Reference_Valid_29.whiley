// Reverse a linked list
type LinkedList<T> is null | &{ T data, LinkedList<T> next }

method reverse<T>(LinkedList<T> l) -> (LinkedList<T> r):
    //
    LinkedList<T> w = null;
    //
    while !(v is null):
        LinkedList<T> t = v.next
        v->next = w
        w = v
        v = t
    //
    return w
