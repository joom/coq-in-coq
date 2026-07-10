(** * Shared infrastructure for the extraction proofs *)

From Stdlib Require Import Arith Lia List Relations Bool Program.Equality.
Import ListNotations.
From CoC Require terms.
From CoC Require typing.
From CoC Require Import confluence.
From CoC Require Import inference.
From CoC Require Import strong_normalization.
From CoC Require Import decidable_conversion.
From BlameFOmega Require syntax infrastructure semantics typing subtyping safety blame subtyping_safety simulation.
From Extraction Require extraction.

Import terms.
Import CoC.typing.
Import extraction.

(** Type-level bidirectional implication (an [iff] that lives in [Type], usable
    when either side is a [Type]-valued proposition such as [has_type],
    [reduces], [convertible], or [is_large]). *)
Definition iffT (A B : Type) : Type := ((A -> B) * (B -> A))%type.

(** Close a goal that is contradictory given an [iffT] between two [is_large]
    facts and two decision results of opposite polarity in context. *)
Ltac iffT_contra Hiff :=
  exfalso;
  match goal with
  | HA : ?A, HB : ?B -> False |- _ => exact (HB (fst Hiff HA))
  | HA : ?B, HB : ?A -> False |- _ => exact (HB (snd Hiff HA))
  end.

(** [is_large] is DECIDABLE: type checking is decidable ([decide_type]), so we can
    compute the reduction-stable classification.  This is the primitive that
    drives the extraction -- replacing the unstable syntactic [classifier]
    with an actual, reduction-stable decision. *)
Definition is_large_dec (e: environment) (T: terms.term) : (is_large e T) + (is_large e T -> False) :=
  decide_type e T (sort_term kind).
