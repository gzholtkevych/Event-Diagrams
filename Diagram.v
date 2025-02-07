Require Import EDiagrams.FiniteSets.
Require Import EDiagrams.Vocabulary.
Require Import Coq.Lists.List.


Section DiagramClass.
Variable participants :
(* refers to the set of diagram participants *)
  FSet PID.
Variable event :
(* picks events related to the diagram *)
  ETag -> Prop.
Variable sending : ETag -> option ETag.
(* refers to the corresponding sending event if the argument is
   a receiving event *)

  Class aDiagram : Prop :=
  (* gathers the constraints relevant to the diagram cocept *)
  { at_least_two :
    (* number of participants is at least two *)
      size participants >= 2
  ; only_participants :
    (* each event related to a diagram is entered in the register of
       some diagram participant *)
      forall e, event e -> In (pid e) participants
  ; all_participants :
    (* for each participant p the event tag with pid = p numbered by 0 is
       event *)
      forall p : PID, In p participants -> event {| pid := p; num := 0 |}
  ; gaplessness :
    (* numbering in each local ledger has no gap *)
      forall e n, event e -> n < num e -> event {| pid := pid e; num := n |}
  ; sending_dom :
    (* 'sending' is defined only for events related to the diagram but
       perhaps not for all *)
      forall e, sending e <> None -> event e
  ; sending_cod :
    (* 'sending' ranges only over events related to the diagrams but
       perhaps not all *)
      forall e e', sending e = Some e' -> event e'
  ; lack_of_sending_to_itself :
    (* there is no manner to send a message from a participant to itself *)
      forall e e', Some e = sending e' -> pid e <> pid e'
  ; sending_injectivity :
    (* each sending event corresponds exactly one receiving event *)
      forall e' e'' e, Some e = sending e' -> Some e = sending e'' -> e' = e''
  }.
End DiagramClass.


Structure Diagram :=
{ participants : FSet PID
; event : ETag -> Prop
; sending : ETag -> option ETag
; diagram_guarantees : aDiagram participants event sending
}.
