

method Triple(x : int) returns (r : int) 
ensures r == 3*x {
    var y := 2*x;
    r := y + x;
    assert r == 3*x;
}


/*
Make methods per stmt?
method Move()
method 

exp = > < > 
mem
var
var
var

Can I access globals or something?


method ()


bil = list stmt
= 
x := store() ;



Literally export the adt
type adt = Move

Write an interpreter?
Do it in Coq?



*/