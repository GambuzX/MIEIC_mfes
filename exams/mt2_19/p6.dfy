// File system node
trait Node {

    const name: string; // unique within each folder
    ghost const depth: nat; // starts in 0 at file system root
}

 class {:autocontracts} File extends Node { }

 class {:autocontracts} Folder extends Node {
   var child: set<Node>; 

    predicate Valid() {
        forall x:Node :: x in child ==> x.depth == this.depth+1 &&
        forall x:Node, y:Node :: x in child && y in child && x != y ==> x.name != y.name
    }

     constructor (name: string, parent: Folder?) 
        requires parent != null ==> forall c :: c in parent.child ==> c.name != name
        requires parent != null ==> parent.Valid()
        modifies parent
        ensures this.name == name
        ensures this.depth == (if parent == null then 0 else parent.depth+1)
        ensures this.child == {}
        ensures parent != null ==> parent.child == old(parent.child) + {this}
        ensures parent != null ==> parent.Valid()
     {
       // this object initialization
        this.name := name;
        this.depth := if parent == null then 0 else parent.depth + 1;
        this.child := {};
        // other objets' updates (after special "new" keyword)
        new;
        if parent != null {
            parent.child := parent.child + {this};
        }
    }
}