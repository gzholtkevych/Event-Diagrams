Require Export EDiagrams.Enum.
Require Import Arith.Compare_dec.
Require Import Lists.List.
Require Import Lia.


Section FSetDefinitions.

  Inductive increasing {X : Set} `{Enum X} : list X -> Prop
  (* The property is that values of the 'tonat' function of list items
     increase                                                                 *)
    := inc_nil : increasing nil
       (* the empty list increases                                            *)
     | inc_sol : forall x, increasing (x :: nil)
       (* a single-item list increases                                        *)
     | inc_cons : forall x y lst,
       (* if to push an item that is before the head of an increasing list into
          this list then the list being obtaned increases *)
         tonat x < tonat y -> increasing (y :: lst) ->
           increasing (x :: y :: lst).

  (* The increasing list of finite set items represents the set.
     The function 'tolist' returns this list.
     Two finite sets are considered equal if their representing lists
     have the same items.
     The size of a finite set is the length of the representing list.
     'empty' refers to the empty set                                          *)
  Definition FSet (X : Set) `{Enum X} := {lst : list X | increasing lst}.

  Definition tolist {X : Set} `{Enum X} (A : FSet X) : list X := proj1_sig A.

  Definition same {X : Set} `{Enum X} (A B : FSet X) : Prop :=
    forall x : X, In x (tolist A) <-> In x (tolist B).

  Definition size {X : Set} `{Enum X} (A : FSet X) : nat := length (tolist A).

  Definition empty {X : Set} `{Enum X} : FSet X.
  Proof. exists nil. constructor. Defined.

End FSetDefinitions.
Coercion tolist : FSet >-> list.
Notation "x == y" := (same x y)  (at level 70).


Section UtilityFacts.
Variable X : Set.
Context `{Enum X}.

  (* The relation 'same' is an equivalence                                    *)
  Lemma same_refl : forall A : FSet X, A == A.
  (* The same relation is reflexive                                           *)
  Proof. firstorder. Qed.

  Lemma same_symm : forall A B : FSet X, A == B -> B == A.
  (* The same relation is symmetric                                           *)
  Proof. firstorder. Qed.

  Lemma same_trans : forall A B C : FSet X, A == B -> B == C -> A == C.
  (* The same relation is transitive                                          *)
  Proof. firstorder. Qed.

  Lemma inc_tail : forall x lst, increasing (x :: lst) -> increasing lst.
  (* The tail of an increasing list increases                                 *)
  Proof. intros. inversion_clear H0; constructor || assumption. Qed.

  Lemma inc_remove :
    forall x lst, increasing lst -> increasing (remove (eq_dec) x lst).
  (* Removing an element from an increasing list gives the list that
     increases                                                                *)
  Proof.
    intros until lst. revert x.
    destruct lst as [| y lst']; intros; auto.
    revert x y H0.
    induction lst' as [| z lst'' IHlst'']; intros; simpl;
    destruct (eq_dec x y) as [H1 | H1]; simpl; try constructor.
    - destruct (eq_dec x z) as [H2 | H2].
      + rewrite <- H1 in H0. rewrite <- H2 in H0. inversion_clear H0.
        exfalso. lia.
      + inversion_clear H0.
        assert (H5 : increasing (remove eq_dec x (z :: lst''))).
        { now apply IHlst''. }
        clear IHlst''. simpl in H5.
        destruct (eq_dec x z) as [H6 | H6]; firstorder.
    - destruct (eq_dec x z) as [H2 | H2].
      + assert (H3 : increasing (remove eq_dec x (y :: lst''))).
        {
          apply IHlst''. inversion_clear H0;
          destruct lst'' as [| u tail].
          - constructor.
          - inversion_clear H4. constructor; [ lia | assumption ].
        }
        simpl in H3. destruct (eq_dec x y) as [H4 | H4]; firstorder.
      + assert (H3 : increasing (remove eq_dec x (z :: lst''))).
        {
          apply IHlst''. now inversion_clear H0.
        }
        simpl in H3. destruct (eq_dec x z) as [H4 | H4]; try contradiction.
        constructor; trivial.
        now inversion_clear H0.
  Qed.

  Lemma lt_head : forall x y lst,
    tonat x < tonat y -> increasing (y :: lst) -> increasing (x :: lst).
    (* Any x is before the head of an increasing list is not in the list tail *)
  Proof.
    intros *. revert x y.
    induction lst as [| z lst' IHlst']; intros.
    - constructor. 
    - inversion_clear H1. constructor; trivial. lia.
  Qed.

  Lemma head_is_min :
    forall x y lst, increasing (x :: lst) -> In y lst -> tonat x < tonat y.
  (* The 'tonat'-value of the head of an increasing list is less
     than 'tonat'-value of any other item of the list                         *)
  Proof.
    intros until lst. revert x y.
    induction lst as [| z lst' IHlst']; intros.
    - contradiction.
    - inversion_clear H0.
      destruct H1 as [H1 | H1];
      [ now rewrite H1 in H2 | apply IHlst']; trivial.
      now apply lt_head with z.
  Qed.

  Definition FS_in_dec (x : X) (A : FSet X) : {In x A} + {~ In x A}.
  (* There is a dicision procedure to check whether an item is in
     an increasing list                                                       *)
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

  Lemma inc_head_not_in_tail :
    forall x lst, increasing (x :: lst) -> ~ In x lst.
  (* The head of an increasing list is not in its tail                        *)
  Proof.
    intros.
    induction lst as [| y lst' IHlst'].
    - intro. contradiction.
    - intro N. destruct N as [H1 | H1].
      + rewrite H1 in H0. inversion_clear H0. lia.
      + revert H1. apply IHlst'. inversion_clear H0.
        destruct lst' as [| z lst'']; constructor;
        [ inversion_clear H2; lia | now apply inc_tail with y ]. 
  Qed.

  Lemma empty_is_nil : forall A, A == empty -> nil = A.
  (* The nil list represemts the empty set                                    *)
  Proof.
    intros (lst, Inc_lst).
    unfold "_ == _". intro. simpl in H0 |-*.
    destruct lst as [| x lst']; trivial.
    exfalso. apply H0 with x. now left.
  Qed.

  Lemma inc_heads :
    forall x1 x2 lst1 lst2,
      increasing (x1 :: lst1) -> increasing (x2 :: lst2) ->
      (forall x, In x (x1 :: lst1) <-> In x (x2 :: lst2)) -> x1 = x2.
  (* If two increasing lists contains same items then their heads are same    *)
  Proof.
    intros * H1 H2 H0.
    destruct (lt_eq_lt_dec (tonat x1) (tonat x2)) as [H3 | H3].
    2: {
      exfalso.
      assert (H4 : tonat x1 < tonat x2).
      {
        apply head_is_min with lst1; trivial.
        pose (H0' := proj2 (H0 x2)). simpl in H0'.
        assert (x1 = x2 \/ In x2 lst1). { apply H0'. now left. }
        destruct H4; trivial.
        exfalso. rewrite H4 in H3. lia.
      }
      lia.
    }
    destruct H3 as [H3 | H3].
    2: { now apply H. }
    exfalso.
    assert (H4 : tonat x2 < tonat x1).
    {
      pose (H0' := proj1 (H0 x1)). simpl in H0'.
      assert (x2 = x1 \/ In x1 lst2). { apply H0'. now left. }
      destruct H4.
      2: { now apply head_is_min with lst2. }
      exfalso. rewrite H4 in H3. lia.
    }
  lia.
  Qed.

  Lemma same_meaning : forall A B, A == B <-> proj1_sig A = proj1_sig B.
  Proof.
    intros (lstA, Inc_lstA) (lstB, Inc_lstB). unfold "_ == _". simpl.
    revert lstA lstB Inc_lstA Inc_lstB.
    induction lstA, lstB; intros.
    - firstorder.
    - firstorder; try (discriminate H0).
      destruct (H0 x). firstorder.
    - firstorder; try (discriminate H0).
      destruct (H0 a). firstorder.
    - firstorder.
      2: { rewrite <- H0. now left. }
      2: { rewrite <- H0. now right. }
      2: { rewrite H0. now left. }
      2: { rewrite H0. now right. }
      pose (H0a := H0 a). pose (H0x := H0 x).
      destruct H0a as (H0a1, _). destruct H0x as (_, H0x2).
      destruct (lt_eq_lt_dec (tonat x) (tonat a)) as [H1 | H1].
      2: {
        assert (tonat x < tonat a).
        {
          assert (In a (x :: lstB)). { apply H0a1. now left. }
          apply head_is_min with lstB; trivial.
          destruct H2; trivial.
          exfalso. rewrite H2 in H1. lia.
         }
         exfalso. lia.
      }
      clear H0a1.
      destruct H1 as [H1 | H1].
      1: {
        assert (tonat a < tonat x).
        {
          assert (In x (a :: lstA)). { apply H0x2. now left. }
          apply head_is_min with lstA; trivial.
          destruct H2; trivial.
          exfalso. rewrite H2 in H1. lia.
        }
        exfalso. lia.
      }
      clear H0x2.
      f_equal.
      1: { symmetry. now apply H. }
      apply IHlstA. clear IHlstA.
      + now apply inc_tail with a.
      + now apply inc_tail with x.
      + intro. pose (H0' := H0 x0). simpl in H0'.
        assert (x = a). { now apply H. }
        rewrite H2 in Inc_lstB. rewrite H2 in H0'.
        destruct H0'.
        destruct (eq_dec a x0) as [H5 | H5]; split; intro.
        * rewrite <- H5 in H6.
          assert (~ In a lstA). { now apply inc_head_not_in_tail. }
          contradiction.
        * rewrite <- H5 in H6.
          assert (~ In a lstB). { now apply inc_head_not_in_tail. }
          contradiction.
        * firstorder.
        * firstorder.
  Qed.

End UtilityFacts.


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
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      1: { destruct H1 as [H1 | H1]; trivial. now constructor. }
      revert y H0 H1.
      induction lst' as [| z lst'' IHlst'']; intros; simpl.
      1: { constructor; constructor || assumption. }
      destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [H2 | H2].
      2: {
        constructor.
        - now inversion_clear H0.
        - apply IHlst''; trivial. now apply inc_tail with y.
      }
      destruct H2 as [H2 | H2]; trivial.
      constructor; trivial.
      constructor; trivial.
      now apply inc_tail with y.
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
      destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
      2: { right. apply IHlst'. now apply inc_tail with y. }
      destruct H1 as [H1 | H1].
      + now left.
      + left. symmetry. now apply H.
  Qed.

  Lemma add_In_x : forall x (A : FSet X), In x A -> A == (add x A).
  Proof.
    intros. apply same_meaning.
    destruct A as (lst, HIA). simpl in H0 |-*.
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
      + assert (tonat y < tonat x). { now apply head_is_min with lst'. }
        lia.
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
      2: {
        destruct lst' as [| z lst''].
        - constructor.
        - simpl in IHlst' |-*.
          destruct (lt_eq_lt_dec (tonat x) (tonat z)) as [H2 | H2].
          2: {
            constructor.
            - now inversion_clear H0.
            - apply IHlst'. now apply inc_tail with y.
          }
          destruct H2 as [H3 | H3]; trivial.
          inversion_clear H0.
          now apply lt_head with z.
      }
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
        * assert (H3 : tonat y < tonat x). { now apply head_is_min with lst'. }
          lia.
      + assert (H3 : tonat y < tonat x). { now apply head_is_min with lst'. }
        rewrite H2 in H3. lia.
  Qed.

  Lemma delete_not_In_x :
    forall x (A : FSet X), ~ In x A -> (delete x A) == A.
  Proof.
    intros x (lst, Inc_lst) N.
    apply same_meaning. simpl.
    induction lst as [| y lst' IHlst']; trivial.
    simpl. destruct (lt_eq_lt_dec (tonat x) (tonat y)) as [H1 | H1].
    2: {
      simpl in N. f_equal.
      assert (Inc_lst' : increasing lst'). { now apply inc_tail with y. }
      firstorder.
    }
    destruct H1 as [H1 | H1]; trivial.
    simpl in N. exfalso. apply N. left. symmetry. now apply H.
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
