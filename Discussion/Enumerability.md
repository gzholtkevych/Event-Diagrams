<H1>Enumerability</H1>

%% insert note text below %%

Here, we give a formal concept of the enumerability of a type (of the sort `Set`). We do this using a technique of type classes in The Coq Proof Assistant.

>[!important] Definition of the class `Enum` 
> ```coq
Class Enum (X : Set) : Type := 
{ tonat : X -> nat
; inj : forall x y : X, tonat x = tonat y -> x = y
}. 

Enumerability of a type ensures 