abstract gt ['a] : 'a -> 'a -> boolean.
abstract ct ['a] : 'a.

goal [any] _ ['a] (x : 'a) : gt x ct.
