(** A point-event is an event without extension in space or time.
    The first point-event component                                          **)
(*    is the identifier of the process that logged the corresponding, and     *)
(** the second point-event component                                         **)
(*    is the timestamp (number) of the event in the log of the process
      that logged the corresponding event                                     *)
Definition PointEvent : Set := nat * nat.
Definition pid (e : PointEvent) : nat := let '(p, _) := e in p.
Definition lts (e : PointEvent) : nat := let '(_, t) := e in t.


(* The class defines constraints on the predicate defined on point-events.
   These constraints provide reasonable requirements in order to consider it
   as the characteristic predicate of an event space.                         *)
Class anEventSpace
  (event_space : PointEvent -> Prop)
  (arrival_trigger : PointEvent -> option PointEvent) : Prop :=
{ (* The timeline of each process is hereditarily closed.                     *)
  theredity : forall e, event_space e -> event_space (pid e, pred (lts e))
; (* The set of participating process identifiers is hereditarily closed.     *)
  sheredity : forall e, event_space e -> event_space (pred (pid e), 0)
; (* The processes identified by 0 and 1 are participants always              *)
  atleast_2 : event_space (0, 0) /\ event_space (1, 0)
; (* The number of participating processes is bounded.                        *)
  sbounded : exists p: nat, forall e, event_space e -> pid e <= p
; (* Point-events of message sending and receiving are in the event space.      *)
  arrival_trigger_dom_codom : forall e e',
    arrival_trigger e = Some e' -> event_space e /\ event_space e'
; (* Message sender and receiver cannot be the same.                          *)
  reciiver_is_not_sender :
    forall e e', arrival_trigger e = Some e' -> pid e <> pid e'
; (* A message arrives to its receiver once only.                             *)
  message_arrives_only_once :
    forall e1 e2 e',
      arrival_trigger e1 = Some e' -> arrival_trigger e2 = Some e' ->
        pid e1 <> pid e2
; (* No point-event refers to both messages sending and receiving
     simultaneously.                                                          *)
  sending_isnot_receiving :
    forall e e', arrival_trigger e' = Some e -> arrival_trigger e = None
; receiving_isnot_sending :
    forall e, arrival_trigger e <> None ->
      forall e', arrival_trigger e' <> Some e
}.


Structure Diagram :=
{ event_space : PointEvent -> Prop
; arrival_trigger: PointEvent -> option PointEvent
; diagram_constraints : anEventSpace event_space arrival_trigger
}.
