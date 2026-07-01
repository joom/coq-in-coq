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


From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOCamlPString.

From CoqInCoq Require Import terms.
From CoqInCoq Require Import confluence.
From CoqInCoq Require Import typing.
From CoqInCoq Require Import decidable_conversion.
From CoqInCoq Require Import inference.
From CoqInCoq Require Import names.
From CoqInCoq Require Import expressions.
From CoqInCoq Require Import machine.

Extract Constant name_eq_dec => "(=)".
Extract Constant name_of_nat => "fun n -> Pstring.unsafe_of_string (""x"" ^ (string_of_int n))".

Extraction
 NoInline list_index is_free_var check_type reduces_to_sort reduces_to_prod execute_axiom
         glob_ctx glob_names empty_state name_dec find_free_var synthesis
         interpret_command translate_message_string translate_error_string interpret_ast.

Extraction "core.ml" is_free_var empty_state interpret_ast.
