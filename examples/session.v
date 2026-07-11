(* Session-typed / typestate protocols in the Calculus of Constructions.

   [Chan s] is a communication channel currently in protocol state [s].  The
   operations are indexed by state, so the protocol's ORDERING is enforced by
   the type system: a channel must be [Ready] to [send], [Sent] before you can
   [recv], and [Done] before you can [close].  Calling [recv] on a fresh
   channel, or [close] twice, is a type error -- an illegal protocol run is
   simply not typeable.

   Axioms declare only the inductive kit: the state constructors, the message
   type with a distinguished [greeting], and the channel family [Chan] with
   constructor [mkchan] and eliminator [chan_rec].  The operations are
   ordinary [Definition]s over a deliberately minimal model -- a channel in
   any state carries the in-flight message, and the "network" echoes it back.
   The protocol discipline lives entirely in the state INDEX, which the model
   never inspects.

   Extraction erases the state index: [Chan s] becomes the plain type [Chan],
   and the protocol operations become ordinary function calls.  The session
   discipline is absent from target types. *)


Axiom St : Set.
Axiom Ready : St.        (* may send   *)
Axiom Sent  : St.        (* may recv   *)
Axiom Done  : St.        (* may close  *)

Axiom Msg : Set.
Axiom greeting : Msg.

(* Channels: an inductive family over states; a channel carries the message
   currently in flight. *)
Axiom Chan : St -> Set.
Axiom mkchan : forall (s : St), Msg -> Chan s.
Axiom chan_rec : forall (s : St) (C : Set), (Msg -> C) -> Chan s -> C.

Definition open : Chan Ready :=
  mkchan Ready greeting.

Definition send (m : Msg) (c : Chan Ready) : Chan Sent :=
  mkchan Sent m.

Definition recv (c : Chan Sent) : Chan Done :=          (* the echo "network" *)
  mkchan Done (chan_rec Sent Msg (fun (m : Msg) => m) c).

Definition close (c : Chan Done) : Msg :=               (* yields the reply *)
  chan_rec Done Msg (fun (m : Msg) => m) c.


(* the one legal run of the protocol: open, send, recv, close.
   Inferred type is just Msg -> Msg: send a request, get a reply. *)

Check fun (req : Msg) => close (recv (send req open)).

Extract fun (req : Msg) => close (recv (send req open)).


(* a client abstract over its starting channel rather than opening one:
   works in any Ready channel and drives it to a reply. *)

Extract fun (req : Msg) (c : Chan Ready) => close (recv (send req c)).


(* just the send step, exposing the state transition Ready -> Sent. *)

Extract fun (req : Msg) (c : Chan Ready) => send req c.


(* the receive-then-close tail, from a Sent channel to the final Msg. *)

Extract fun (c : Chan Sent) => close (recv c).
