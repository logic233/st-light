Require Import ST_Operators.
Require Export ST_Syntax.
Require Export ST_Semantics.
Require Export ST_Typing.

From Velus Require Import Common.

Module Type ST (Ids: IDS) (Op: ST_OPERATORS) (OpAux: OPERATORS_AUX Op).
  Declare Module Export Syn: ST_SYNTAX      Ids Op OpAux.
  Declare Module Export Sem: ST_SEMANTICS   Ids Op OpAux Syn.
  Declare Module Export Typ: ST_TYPING      Ids Op OpAux Syn Sem.

End ST.

Module ST_Fun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       <: ST Ids Op OpAux.
  Module Export Syn := ST_SyntaxFun      Ids Op OpAux.
  Module Export Sem := ST_SemanticsFun   Ids Op OpAux Syn.
  Module Export Typ := ST_TypingFun      Ids Op OpAux Syn Sem.
End ST_Fun.