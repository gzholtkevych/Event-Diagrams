Require Export Arith.PeanoNat.


Class Enum (X : Set) :=
(* Definition of the Enum class depends on a type of sort Set *)
{ tonat : X -> nat
  (* X is equipped with a function mapping its elements into natural numbers *)
; tonat_inj : forall x y, tonat x = tonat y -> x = y
  (* that function should be injective *)
}.


Definition eq_dec {X : Set} `{Enum X} : forall x y : X, {x = y} + {x <> y}.
(* Decision procedure for equality based on the Enum class *)
Proof.
  intros.
  destruct (Nat.eq_dec (tonat x) (tonat y)) as [H0 | H0].
  - (** Case: tonat x = tonat y **)
    left. now apply tonat_inj.
  - (** Case: tonat x <> tonat y **)
    right. intro H'. apply H0. now rewrite H'.
Defined.


Instance enum_nat : Enum nat.
(* Enum instance for type nat *)
Proof.
  pose (tonat := fun x : nat => x).
  constructor 1 with tonat. intros.
  now compute in H.
Defined.
