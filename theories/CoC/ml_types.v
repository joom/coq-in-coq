(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(** Concrete types for the extracted type-checker:
    [nat] for integers (extracted to OCaml [int] via ExtrOcamlNatInt)
    and [PrimString.string] for names (extracted via ExtrOCamlPString). *)

From Stdlib Require Import PString.

(** The type of names, backed by primitive strings. *)
Definition name : Set := PrimString.string.

(** Decidable equality on names via primitive string comparison. *)
Definition name_eq_dec : forall s1 s2 : name, {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct (PrimString.compare s1 s2) eqn:H.
  - left. apply compare_eq. exact H.
  - right. intro Heq. subst. rewrite compare_refl in H. discriminate.
  - right. intro Heq. subst. rewrite compare_refl in H. discriminate.
Defined.

(** Injective name generation from naturals.
    Axiomatized and extracted as [fun n -> "x" ^ string_of_int n]. *)
Parameter name_of_nat : nat -> name.
Axiom name_of_nat_inj : forall m n : nat, name_of_nat m = name_of_nat n -> m = n.
