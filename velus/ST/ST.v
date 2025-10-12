(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

Require Import ST_Operators.
Require Export ST_Syntax.
Require Export ST_Semantics.
Require Export ST_Typing.

From Velus Require Import Common.

Module Type ST (Ids: IDS) (Op: ST_OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: ST_SYNTAX      Ids Op OpAux.
  Declare Module Export Sem: ST_SEMANTICS   Ids Op OpAux Syn.
  (* Declare Module Export Inv: OBCINVARIANTS  Ids Op OpAux Syn Sem. *)
  Declare Module Export Typ: OBCTYPING      Ids Op OpAux Syn Sem.
  (* Declare Module Export Equ: EQUIV          Ids Op OpAux Syn Sem     Typ. *)
  (* Declare Module Export Fus: FUSION         Ids Op OpAux Syn Sem Inv Typ Equ. *)
  (* Declare Module Export Def: OBCADDDEFAULTS Ids Op OpAux Syn Sem Inv Typ Equ. *)
End ST.

Module ST_Fun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: ST Ids Op OpAux.
  Module Export Syn := ST_SyntaxFun      Ids Op OpAux.
  Module Export Sem := ST_SemanticsFun   Ids Op OpAux Syn.
  (* Module Export Inv := ObcInvariantsFun  Ids Op OpAux Syn Sem. *)
  Module Export Typ := ObcTypingFun      Ids Op OpAux Syn Sem.
  (* Module Export Equ := EquivFun          Ids Op OpAux Syn Sem     Typ. *)
  (* Module Export Fus := FusionFun         Ids Op OpAux Syn Sem Inv Typ Equ. *)
  (* Module Export Def := ObcAddDefaultsFun Ids Op OpAux Syn Sem Inv Typ Equ.  *)
End ST_Fun.