type Node is &{
    int nodeType
}
type Document is &{
    method appendChild(Node)
}

method append(Node n):
    n->nodeType = 0

public export method test():
    Document doc = new { appendChild: &append }
    Node node = new { nodeType: 1 }
    doc->appendChild(node)
    assume node->nodeType == 0
