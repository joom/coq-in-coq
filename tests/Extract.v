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

From CoC Require Import terms.
From CoC Require Import confluence.
From CoC Require Import typing.
From CoC Require Import decidable_conversion.
From CoC Require Import inference.
From CoC Require Import names.
From CoC Require Import expressions.
From CoC Require Import machine.
From BlameFOmega Require syntax infrastructure semantics typing subtyping safety blame subtyping_safety simulation.
From BlameFOmega Require expressions.
From Extraction Require extraction.
From Extraction Require proofs.
From Extraction Require translation.

Set Extraction Output Directory "tests".

Extract Inductive name => "string"
  ["Fun.id" "(fun n -> Pstring.unsafe_of_string (""x"" ^ string_of_int n))"]
  "(fun f_str f_gen s -> f_str s)".
Extract Constant name_eq_dec => "(=)".

Extraction
 NoInline list_index is_free_var check_type reduces_to_sort reduces_to_prod execute_axiom
         glob_ctx glob_names empty_state name_dec find_free_var synthesis
         interpret_command translate_message_string translate_error_string interpret_ast.

Extraction "core.ml" is_free_var empty_state interpret_ast
  synthesis infer translation.extract
  collect_binder_names
  BlameFOmega.expressions.fterm_expression_of BlameFOmega.expressions.ftyp_expression_of
  BlameFOmega.expressions.fterm_expr BlameFOmega.expressions.ftyp_expr.
