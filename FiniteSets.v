Require Export EDiagrams.Enum.
Require Import Arith.Compare_dec.
Require Import Lists.List.
Require Import Lia.

Section FSetDefinitions.
Variable X : Set.
Context `{Enum X}.

  Inductive increasing : list X -> Prop :=
  | inc_nil : increasing nil
  | inc_sol : forall x, increasing (x :: nil)
  | inc_cons : forall x y lst,
      tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: y :: lst).

  Definition FSet := {lst : list X | increasing lst}.

  Definition tolist (A : FSet) : list X := proj1_sig A.

  Definition same (A B : FSet) : Prop :=
    forall x : X, In x (tolist A) <-> In x (tolist B).

End FSetDefinitions.
Arguments increasing {X} {_}.
Arguments same {X} {_}.
Coercion tolist : FSet >-> list.
Notation "x =:= y" := (same x y)  (at level 70).


Definition size {X : Set} `{Enum X} (A : FSet X) : nat := length A.


Definition empty {X : Set} `{Enum X} : FSet X.
Proof. exists nil. constructor. Defined.


Section BasicFacts.
Variable X : Set.
Context `{Enum X}.

  Lemma same_refl : forall A : FSet X, A =:= A.
  Proof.
    intro. destruct A as (lst, HInc).
    unfold "_ =:= _". intro. simpl. now split.
  Qed.

  Lemma same_symm : forall A B : FSet X, A =:= B -> B =:= A.
  Proof.
    intros *. unfold "_ =:= _". intros.
    split; intro; now apply H0.
  Qed.

  Lemma same_trans : forall A B C : FSet X, A =:= B -> B =:= C -> A =:= C.
  Proof.
    intros *. unfold "_ =:= _". intros.
    split; intro.
    - apply H1. now apply H0.
    - apply H0. now apply H1.
  Qed.

  Lemma inc_tail :
    forall x lst, increasing (x :: lst) -> increasing lst.
  Proof. intros. inversion_clear H0; constructor || assumption. Qed.

  Lemma inc_without :
    forall x y lst, increasing (x :: y :: lst) -> increasing (x :: lst).
  Proof.
    intros.
    destruct lst as [| z lst'].
    - constructor.
    - inversion_clear H0. inversion_clear H2.
      constructor; trivial. now apply Nat.lt_trans with (tonat y).
  Qed.

  Lemma head_is_min :
    forall x y lst, increasing (x :: lst) -> In y lst -> tonat x < tonat y.
  Proof.
    intros until lst. revert x y.
    induction lst as [| z lst' IHlst']; intros.
    - contradiction.
    - destruct H1.
      + inversion_clear H0. now rewrite H1 in H2.
      + apply IHlst'; trivial. now apply inc_without with z.
  Qed.

  Definition FS_in_dec (x : X) (A : FSet X) : {In x A} + {~ In x A}.
  Proof.
    destruct A as (lst, HInc). simpl.
    induction lst as [| y lst' IHlst'].
    - right. intro. contradiction.
    - destruct (eq_dec y x) as [H1 | H1].
      + left. now left.
      + assert (H2 : {In x lst'} + {~ In x lst'}).
        { apply IHlst'. now apply inc_tail with y. }
        destruct H2 as [H2 | H2]; [left | right]; try now right.
        intro H3. elim H3; trivial.
  Defined.

  Lemma inc_not_in_lst : forall x lst, increasing (x :: lst) -> ~ In x lst.
  Proof.
    intros.
    induction lst as [| y lst' IHlst'].
    - intro. contradiction.
    - intro N. destruct N as [H1 | H1].
      + rewrite H1 in H0. inversion_clear H0.
        now apply Nat.lt_irrefl with (tonat x).
      + revert H1. apply IHlst'. inversion_clear H0.
        destruct lst' as [| z lst'']; try constructor.
        * apply Nat.lt_trans with (tonat y); trivial.
          apply head_is_min with (z :: lst''); trivial. now left.
        * now apply inc_tail with y. 
  Qed.

  Lemma lt_head : forall x y lst,
    tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: lst).
  Proof.
    intros *. revert x y.
    induction lst as [| z lst' IHlst']; intros.
    - constructor. 
    - inversion_clear H1. constructor; trivial. lia.
  Qed.

  Lemma empty_is_nil : forall A, A =:= empty -> nil = A.
  Proof.
    intro. destruct A as (lst, HI).
    unfold same. intro. simpl in H0 |-*.
    destruct lst as [| x lst']; trivial.
    exfalso. apply (H0 x). now left.
  Qed.

  Lemma inc_heads :
    forall x1 x2 lst1 lst2,
      increasing (x1 :: lst1) -> increasing (x2 :: lst2) ->
      (forall x, In x (x1 :: lst1) <-> In x (x2 :: lst2)) -> x1 = x2.
  Proof.
    intros * H1 H2 H0.
    destruct (lt_eq_lt_dec (tonat x1) (tonat x2)) as [H3 | H3].
    2: {
      exfalso. apply Nat.lt_irrefl with (tonat x1).
      apply Nat.lt_trans with (tonat x2); trivial.
      apply head_is_min with lst1; trivial.
      destruct (H0 x2) as (_, H4). simpl in H4.
      assert (H5 : x1 = x2 \/ In x2 lst1). { apply H4. now left. }
      destruct H5 as [H5 | H5]; trivial.
      exfalso. rewrite H5 in H3. lia.
    }
    destruct H3 as [H3 | H3].
    2: { now apply H. }
    exfalso. apply Nat.lt_irrefl with (tonat x1).
    apply Nat.lt_trans with (tonat x2); trivial.
    apply head_is_min with lst2; trivial.
    destruct (H0 x1) as (H4, _). simpl in H4.
    assert (x2 = x1 \/ In x1 lst2). { apply H4. now left. }
    destruct H5 as [H5 | H5]; trivial.
    exfalso. rewrite H5 in H3. lia.
  Qed.

  Lemma same_meaning :
    forall A B, A =:= B <-> exists lst : list X, lst = A /\ lst = B.
  Proof.
    intros.
    destruct A as (lstA, HIA). destruct B as (lstB, HIB). simpl.
    unfold same. simpl. revert lstA lstB HIA HIB.
    induction lstA, lstB; intros; split; intro.
    - exists nil. split; trivial.
    - intro. split; trivial.
    - exfalso. simpl in H0. apply H0 with x. now left.
    - intro. split; intro; try contradiction.
      do 2 destruct H0. rewrite H0 in H2. discriminate H2.
    - exfalso. simpl in H0. apply H0 with a. now left.
    - exfalso. destruct H0 as (lst, H0). destruct H0. rewrite H1 in H0.
      discriminate H0.
    - assert (x = a).
      {
        apply inc_heads with lstB lstA; trivial.
        intro. destruct (H0 x0). split; intro; [ now apply H2 | now apply H1 ].
      }
      rewrite H1 in H0, HIB |-*.
      exists (a :: lstA). split; trivial.
      f_equal.
      assert (IH : (forall x : X, In x lstA <-> In x lstB) <->
        (exists lst : list X, lst = lstA /\ lst = lstB)).
      { apply IHlstA; now apply inc_tail with a. }
      assert (H0' : forall x : X, In x lstA <-> In x lstB).
      {
        intro. destruct (eq_dec x0 a) as [H2 | H2].
        - rewrite H2. split; intro;
          [ pose (inc_not_in_lst a lstA HIA)
          | pose (inc_not_in_lst a lstB HIB) ];
          contradiction.
        - destruct (H0 x0). simpl in H3, H4. split; intro.
          + assert (H3' : a = x0 \/ In x0 lstB). { apply H3. now right. }
            destruct H3' as [H3' | H3']; trivial.
            symmetry in H3'. contradiction.
          + assert (H4' : a = x0 \/ In x0 lstA). { apply H4. now right. }
            destruct H4' as [H4' | H4']; trivial.
            symmetry in H4'. contradiction.
      }
      destruct IH as (H2, _). destruct (H2 H0') as (lst, H3).
      destruct H3 as (H31, H32). now rewrite H31 in H32.
    - destruct H0 as (lst, H0). destruct H0.
      rewrite <- H0. rewrite <- H1. intro. split; intro; trivial.
  Qed.

End BasicFacts.


Section AddOperation.
Variable X : Set.
Context `{Enum X}.

  Fixpoint aux_add (x : X) (lst : list X) : list X :=
    match lst with
    | nil       => x :: nil
    | y :: lst' => match lt_eq_lt_dec (tonat x) (tonat y) with
        | inleft Hle => match Hle with
            | left _  => x :: y :: lst'
            | right _ => y :: lst'
            end
        | inright _  => y :: (aux_add x lst')
        end
    end.

  Lemma aux_add_keeps_increasing :
    forall x lst, increasing lst -> increasing (aux_add x lst).
  Proof.
    intros *.
    destruct lst as [| y lst'].
    - intros. constructor.
    - intros. simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now constructor.
      + assumption.
      + revert y H0 Hgt.
        induction lst' as [| z lst'' IHlst'']; intros; simpl.
        * constructor; constructor || assumption.
        * destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [Hle | Hgt'];
          try destruct Hle as [Hlt | Heq]; constructor; trivial;
          try constructor; trivial;
          try (now apply inc_tail with y);
          try (inversion_clear H0; trivial).
          now apply IHlst''.
  Qed.

  Definition add (x : X) (A : FSet X) : FSet X.
  Proof.
      destruct A as (lst, HInc).
      exists (aux_add x lst).
      destruct lst as [| y lst'].
      - constructor.
      - now apply aux_add_keeps_increasing.
  Defined.

  Lemma add_In : forall x A, In x (add x A).
  Proof.
    intros x A. destruct A as (lst, H0). simpl.
    induction lst as [| y lst' IHlst'].
    - now left.
    - simpl.
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [Hle | Hgt];
      try destruct Hle as [Hlt | Heq].
      + now left.
      + left. symmetry. now apply H.
      + right. apply IHlst'. now apply inc_tail with y.
  Qed.

  Lemma add_In_x : forall x (A : FSet X), In x A -> same A (add x A).
  Proof.
    intros. apply same_meaning.
    destruct A as (lst, HIA). exists lst. simpl.
    split; trivial.
    simpl in H0.
    induction lst as [| y lst' IHlst'].
    - contradiction.
    - simpl. destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      2: {
        destruct H0 as [H0 | H0].
        - exfalso. rewrite H0 in H1. lia.
        - f_equal. apply IHlst'; trivial. now apply inc_tail with y.
      }
      destruct H1 as [H1 | H1]; trivial.
      exfalso. destruct H0 as [H0 | H0].
      + rewrite H0 in H1. lia.
      + apply Nat.lt_irrefl with (tonat x).
        apply Nat.lt_trans with (tonat y); trivial.
        now apply head_is_min with lst'.
  Qed.
End AddOperation.
Arguments add {X} {_}.


Fixpoint fromlist {X : Set} `{Enum X} (lst : list X) : FSet X :=
  match lst with
  | nil => empty
  | x :: lst' => add x (fromlist lst')
  end.


Section RemoveOperation.
Variable X : Set.
Context `{Enum X}.

  Fixpoint aux_delete (x : X) (lst : list X) : list X :=
    match lst with
    | nil       => nil
    | y :: lst' =>
        match lt_eq_lt_dec (tonat x) (tonat y) with
        | inleft Hle  =>
            match Hle with
            | left _  => (y :: lst')
            | right _ => lst'
            end
        | inright _   => y :: (aux_delete x lst')
        end
    end.

  Lemma aux_delete_keeps_increasing :
    forall x lst, increasing lst -> increasing (aux_delete x lst).
  Proof.
    intros *.
    induction lst as [| y lst' IHlst']; intros.
    - trivial.
    - simpl. destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      2: { destruct lst' as [| z lst''].
           - constructor.
           - simpl in IHlst' |-*.
             destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [H2 | H2].
             2: { constructor.
                  - now inversion_clear H0.
                  - apply IHlst'. now apply inc_tail with y. }
             destruct H2 as [H3 | H3]; trivial.
             now apply inc_without with z. }
      destruct H1 as [H2 | H2]; trivial.
      now apply inc_tail with y.
  Qed.

  Definition delete (x : X) (A : FSet X) : FSet X.
  Proof.
    destruct A as (lst, H0).
    exists (aux_delete x lst).
    now apply aux_delete_keeps_increasing.
  Defined.

  Lemma delete_not_In : forall x A, ~ In x (delete x A).
  Proof.
    intros x (lst, H0) N. simpl in N.
    induction lst as [| y lst' IHlst']; simpl in N.
    - contradiction.
    - destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      2: {
        apply IHlst'.
        - now apply inc_tail with y.
        - destruct N as [H2 | H2]; trivial. exfalso. rewrite H2 in H1. lia.
      }
      destruct H1 as [H2 | H2].
      + destruct N.
        * exfalso. rewrite H1 in H2. lia.
        * assert (H3 : tonat y < tonat x).
          { now apply head_is_min with lst'. }
          lia.
      + assert (H3 : tonat y < tonat x).
        { now apply head_is_min with lst'. }
        rewrite H2 in H3. lia.
  Qed.

  Lemma delete_not_In_x :
    forall x (A : FSet X), ~ In x A -> same (delete x A) A.
  Proof.
    intros x (lst, Inc_lst) N.
    apply same_meaning. simpl.
    exists lst. split; trivial.
    induction lst as [| y lst' IHlst'].
    - reflexivity.
    - simpl. destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      2: {
        simpl in N. f_equal.
        assert (Inc_lst' : increasing lst'). { now apply inc_tail with y. }
        apply IHlst' with Inc_lst'. intro. simpl in H0. apply N. now right.
      }
      destruct H1 as [H1 | H1]; trivial.
      simpl in N.
      exfalso. apply N. left. symmetry. now apply H.
  Qed.

End RemoveOperation.
Arguments delete {X} {_}.


Section Filtration.
Variable X : Set.
Context `{Enum X}.

  Definition subset (A B : FSet X) : Prop := forall x : X, In x A -> In x B.

  Lemma subset_same : forall A B, A =:= B <-> subset A B /\ subset B A.
  Proof.
    intros. split.
    - intro. split; unfold subset; intro; now destruct H0 with x.
    - intros; unfold subset in H0. destruct H0.
      split; [ exact (H0 x) | exact (H1 x) ].
  Qed.
  Notation "x << y" := (subset x y) (at level 70).

  Fixpoint keep_if (lst : list X) (f : X -> bool) : list X :=
    match lst with
    | nil => nil
    | x :: lst' => if f x then x :: (keep_if lst' f)
                   else keep_if lst' f
    end.

  Lemma keep_if_sub_lst : forall (lst : list X) (f : X -> bool) x,
    In x (keep_if lst f) -> In x lst.
  Proof.
    intros.
    induction lst as [| y lst' IHlst'].
    - contradiction.
    - simpl in H0. destruct (f y).
      + simpl in H0 |-*. destruct H0 as [H0 | H0];
        [ now left | right; now apply IHlst' ].
      + right. now apply IHlst'.
  Qed. 

  Lemma keep_if_keep_inc :
    forall (lst : list X) (f : X -> bool),
      increasing lst -> increasing (keep_if lst f).
  Proof.
    intros.
    induction H0; simpl; try destruct (f x);
    try constructor; simpl in IHincreasing; destruct (f y); trivial.
    1: now constructor.
    destruct (keep_if lst f) as [| z lst'] eqn: E.
    - constructor.
    - constructor; trivial.
      assert (In z (y :: lst)).
      {
        simpl. destruct (eq_dec y z).
        - now left.
        - right. apply keep_if_sub_lst with f. rewrite E. now left.
      }
      destruct (lt_eq_lt_dec (tonat y) (tonat z)) as [H3 | H3].
      2: { 
        exfalso. apply Nat.lt_irrefl with (tonat z).
        apply Nat.lt_trans with (tonat y); trivial.
        apply head_is_min with lst; trivial.
        destruct H2 as [H2 | H2]; trivial.
        exfalso. rewrite H2 in H3. lia.
      }
      destruct H3 as [H3 | H3].
      + lia.
      + now rewrite <- H3.
  Qed.

  Definition gen_dif (A : FSet X) (f : X -> bool) : FSet X.
  Proof.
    destruct A as (lst, Inc_lst).
    pose (lst' := keep_if lst f).
    exists lst'. now apply keep_if_keep_inc.
  Defined.

  Lemma gen_dif_sub : forall A f, gen_dif A f << A.
  Proof.
    intros (lst, Inc_lst) *. unfold "_ << _". intros. unfold gen_dif in H0.
    simpl in H0 |-*.
    induction lst as [| y lst' IHlst'].
    - contradiction.
    - simpl in H0 |-*.
      destruct (f y).
      + simpl in H0. destruct H0.
        * now left.
        * right. apply IHlst'; trivial. now apply inc_tail with y.
      + right. apply IHlst'.
        * now apply inc_tail with y.
        * assumption.
  Qed.

End Filtration.
Arguments subset {X} {_}.
Notation "x << y" := (subset x y) (at level 70).
