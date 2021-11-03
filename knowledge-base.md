# Knowledge Base

The BAP knowledge base is a centralized store of information meant to hold all the things discovered about a binary. This include properties like the architecture, addresses, and lifted code. Ideally, many user defined analysis may intercommunicate by storing their results into the knowledge base.

The term knowledge base may mean nothing more than database, but to me it implies that it is a combination of a database and mechanisms to automatically derive or populate more information.


### Classes, Slots, Values.




# Extensible Records

Ordinary ocaml record look like
`type myrecord = {myint : int; mybool : bool}`

Bap is designed as a framework however, so it is desirable for the record types used by bap to be user extensible. This is a challenge in a statically typed language.

The Bap type `Dict.t` is an extensible record.

# `Record.t` = `Dict.t` + Domains

It is desirable for bap to define a notion of record merging. This is a useful concept if you want to combine information built by different pieces of code into a single record.
One way of doing this is require each field implement the `domain` interface, so that you can merge record by merging each field individually.
The common case is that some code may only fill out certain fields of the record and other code other disjoint fields. The empty fields are represented by ocaml `None` values. Then the merge you want is the record with all the fields filled out. This is the optional domain.
Another common case is to merge a field that is a set by using the union or intersection of those sets. 

# Value = Record + Sorts


#









Discussion of Ivan's talk https://gitter.im/BinaryAnalysisPlatform/bap?at=614c7f4c1179346966327e8c
