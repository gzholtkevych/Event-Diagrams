Require Import STDiagrams.Diagrams.
Require Import Coq.Arith.PeanoNat.
Require Import Arith.Compare_dec.
Require Import Lists.List.


  Inductive happen_before (dgm : Diagram) : PointEvent -> PointEvent -> Prop :=
  | hbtimeline :
    (* if two events have the same source then their causal order is
       the order of their numbers in the local ledger of their source *)
      forall e1 e2 : PointEvent, event dgm e1 -> event dgm e2 ->
        pid e1 = pid e2 -> lts e1 < lts e2 -> happen_before dgm e1 e2
  | hbarrive :
    (* the sending event of a message causes the receiving of this message *)
      forall e1 e2, triggering dgm e2 = Some e1 -> happen_before dgm e1 e2
  | hbtrans :
    (* the causal order is transitive *)
      forall e1 e2 e3,
        happen_before dgm e1 e2 -> happen_before dgm e2 e3 ->
          happen_before dgm e1 e3.

Notation "z [ x --> y ]" := (happen_before z x y)  (at level 70).


Lemma happen_before_event_space :
(*  *)
  forall dgm e1 e2, dgm[e1 --> e2] -> event dgm e1 /\ event dgm e2.
Proof.
  intro. destruct (diagram_constraints dgm). intros.
  induction H; split; firstorder.
Qed. 


Section NoIrreflexivity.

  Definition event0 := fun e : PointEvent => pid e = 0 \/ pid e = 1.
  Definition triggering0 := fun e : PointEvent =>
    let '(p, t) := e in
    match p with
    | 0 => match t with
           | 0 => Some (1, 1)
           | _ => None
           end
    | 1 => match t with
           | 0 => Some (0, 1)
           | _ => None
           end
    | _ => None
    end.

  Lemma dom_triggering0 :
    forall e e' : PointEvent, triggering0 e = Some e' -> triggering0 e <> None.
  Proof. intros. intro. rewrite H0 in H. discriminate H. Qed.

  Lemma cod_triggering0 :
    forall e : PointEvent, triggering0 e <> None -> e = (0, 0) \/ e = (1, 0).
  Proof.
    intros. destruct e as (p, t).
    destruct p as [| p]; try destruct p as [| p];
    destruct t as [| t]; try destruct t as [| t]; compute in H;
    try contradiction; [left | right]; trivial.
  Qed.

  Instance H : aDiagram event0 triggering0.
  Proof.
    constructor.
    - firstorder.
    - firstorder; rewrite H; firstorder.
    - firstorder.
    - exists 1. firstorder; rewrite H; constructor. constructor.
    - intros.
      assert (triggering0 e <> None). { now apply dom_triggering0 with e'. }
      assert (e = (0, 0) \/ e = (1, 0)). { now apply cod_triggering0. }
      split.
      + destruct H1 as [H1 | H1]; rewrite H1; compute; [left | right]; trivial.
      + destruct H1 as [H1 | H1]; rewrite H1 in H; compute in H;
        injection H; intro; rewrite <- H2; compute; [right | left]; trivial.
    - intros.
      assert (triggering0 e <> None). { now apply dom_triggering0 with e'. }
      assert (e = (0, 0) \/ e = (1, 0)). { now apply cod_triggering0. }
      destruct H1 as [H1 | H1]; rewrite H1 in H |-*; compute in H;
      injection H; intro; rewrite <- H2; compute; intro; discriminate H3.
    - intros.
      assert (triggering0 e1 <> None). { now apply dom_triggering0 with e'. }
      assert (e1 = (0, 0) \/ e1 = (1, 0)). { now apply cod_triggering0. }
      assert (triggering0 e2 <> None). { now apply dom_triggering0 with e'. }
      assert (e2 = (0, 0) \/ e2 = (1, 0)). { now apply cod_triggering0. }
      destruct H3 as [H3 | H3], H5 as [H5 | H5].
      + rewrite <- H5 in H3. contradiction.
      + rewrite H3 in H. compute in H. rewrite H5 in H0. compute in H0.
        rewrite <- H0 in H. injection H. intro. discriminate H6.
      + rewrite H3 in H. compute in H. rewrite H5 in H0. compute in H0.
        rewrite <- H0 in H. injection H. intro. discriminate H6.
      + rewrite <- H5 in H3. contradiction.
    - intros.
      assert (triggering0 e' <> None). { now apply dom_triggering0 with e. }
      assert (e' = (0, 0) \/ e' = (1, 0)). { now apply cod_triggering0. }
      destruct H1 as [H1 | H1]; rewrite H1 in H; compute in H; injection H;
      intro; rewrite <- H2; compute; trivial.
    - intros. intro.
      assert (triggering0 e' <> None). { now apply dom_triggering0 with e. }
      assert (e' = (0, 0) \/ e' = (1, 0)). { now apply cod_triggering0. }
      destruct H2 as [H2 | H2]; rewrite H2 in H0; compute in H0;
      injection H0; intro; rewrite <- H3 in H; compute in H; apply H; trivial.
  Defined.

  Definition deadlock : Diagram :=
    {| event := event0; triggering := triggering0; diagram_constraints := H |}.

  Lemma deadlock_presence :
    deadlock[(0, 0) --> (0, 0)].
  Proof.
    constructor 3 with (e2 := (0, 1)).
    - constructor 1; compute; try left; trivial.
    - constructor 3 with (e2 := (1, 0)).
      + constructor 2; trivial.
      + constructor 3 with (e2 := (1, 1)).
        * constructor 1; compute; trivial; right; trivial.
        * constructor 2. now compute.
  Qed.
End NoIrreflexivity.


Section Clocks.
Variable dgm : Diagram.

  Class aClock (ts : PointEvent -> nat -> Prop) : Prop :=
  { clock_dom : forall e, event dgm e <-> exists t, ts e t
  ; clock_func : forall e t1 t2, ts e t1 -> ts e t2 -> t1 = t2
  ; clock_mono : forall e1 e2 t1 t2,
      dgm[e1 --> e2] -> ts e1 t1 -> ts e2 t2 -> t1 < t2
  }. 

Definition Clock := { clock : PointEvent -> nat -> Prop | aClock clock }.

End Clocks.


Theorem clock_irrefl : forall dgm, (exists ts, aClock dgm ts) ->
  forall e, ~ dgm[e --> e].
Proof.
  intros. destruct H0 as (ts, H0). destruct H0 as (H1, H2, H3).
  intro.
  destruct (H1 e) as (H11, H12).
  assert (exists t : nat, ts e t).
  {
    apply H11. now apply (happen_before_event_space dgm e).
  }
  destruct H4 as (t, H4).
  assert (t < t). {
    apply H3 with (e1 := e) (e2 := e); trivial;
    apply H4; pose (proj1 (happen_before_event dgm e e H)); assumption.
  }
  now apply Nat.lt_irrefl with t.
Qed.


Section Irreflexivity.
Variable dgm : Diagram.
Hypothesis HIrr : forall e, ~ dgm[e --> e].

  Definition launcher (p : PID) : option PID :=
    (* returns the launcher of p if p is in participants and a launcher exists
       otherwise returns None *)
    if FS_in_dec PID p (participants dgm) then
      match sending dgm {| pid := p; num := 0 |} with
      | Some e => Some (pid e)
      | None   => None
      end
    else None.

  Lemma hb_launcher : forall p q,
    Some q = launcher p ->
      dgm[{| pid := q; num := 0|} --> {| pid := p; num := 0 |}].
  Proof.
    intros. destruct (launcher p) as [r |].
    - constructor.
    - unfold launcher in H.

  Definition is_initiator (p : PID) : bool :=
  (* returns true if In p (particiapnts dgm) and
             sending dgm {| pid := p; num := 0 |} = None
             otherwise returns false *)
      match launcher p with
      | Some _ => false
      | None   =>
          if FS_in_dec PID p (participants dgm) then true
          else false
      end.

  Lemma is_initiator_correct :
    forall p : PID, is_initiator p = true <-> In p (participants dgm) /\
      sending dgm {| pid := p; num := 0 |} = None.
  Proof.
    intro. split; intro H.
    - unfold is_initiator in H.
      unfold launcher in H.
      destruct (FS_in_dec PID p (participants dgm)) as [H0 | H0];
      destruct (sending dgm {| pid := p; num := 0 |});
      try discriminate H. split; trivial.
    - destruct H as (H1, H2). unfold is_initiator. unfold launcher.
      destruct (FS_in_dec PID p (participants dgm)) as [H0 | H0].
      2: { contradiction. }
      destruct (sending dgm {| pid := p; num := 0 |}); trivial.
      discriminate H2.
  Qed.

  Definition initiators := gen_dif PID (participants dgm) is_initiator.

  Lemma initiators_sub_participants : initiators << participants dgm.
  Proof. unfold initiators. apply gen_dif_sub. Qed.

  Lemma not_empty_initiators : ~ initiators =:= empty.
  Proof.
    intro. unfold "_ =:= _" in H.
    destruct (participants dgm) as (lst, Inc_lst).
    simpl in H.

  Inductive lamport : ETag -> nat -> Prop :=
  | lamp0 :
      forall e, event dgm e ->
        sending dgm e = None -> num e = 0 -> lamport e 0
  | lampl :
      forall e e' t, event dgm e ->
        sending dgm e = None -> pid e = pid e' -> num e = S (num e') ->
          lamport e' t -> lamport e (S t)
  | lamps :
      forall e e1 e2 t1 t2, event dgm e ->
        sending dgm e = Some e1 ->
        pid e = pid e2 -> num e = S (num e2) ->
          lamport e1 t1 -> lamport e2 t2 -> lamport e (S (max t1 t2)).











