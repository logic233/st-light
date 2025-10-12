From Coq Require Import ZArith.BinInt.
From Coq Require Import String.
From Coq Require Import List.

From compcert Require cfrontend.Clight.
From compcert Require Import lib.Integers.
From compcert Require Import common.Errors.
From compcert Require Import lib.Maps.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Environment.
Require Import ST_Interface.
From Velus Require Import Ident.
Require Import ST.
Print ST.
Import ST.Syn  .
(* Import ST.Typ. *)

Open Scope error_monad_scope.
Open Scope Z.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import FMapAVL.
From Coq Require Export Structures.OrderedTypeEx.

Module IdentPair := PairOrderedType Positive_as_OT Positive_as_OT.
Module M := FMapAVL.Make(IdentPair).

(**************************************************)
(*func_name == prefix ID_RESET POU_ID*)

Definition ID_RESET := pos_of_str "fun_reset".
(*func_name == prefix ID_EXEC POU_ID*)
Definition ID_EXEC := pos_of_str "fun_exce".
(**************************************************)


(* TRANSLATION *)
Definition type_of_inst (o: ident): Ctypes.type :=
  Ctypes.Tstruct o Ctypes.noattr.
Definition pointer_of (ty: Ctypes.type): Ctypes.type :=
  Ctypes.Tpointer ty Ctypes.noattr.
Definition type_of_inst_p (o: ident): Ctypes.type :=
  pointer_of (type_of_inst o).

Definition deref_field (id po x: ident) (xty: Ctypes.type): Clight.expr :=
  let ty_deref := type_of_inst po in
  let ty_ptr := pointer_of ty_deref in
  Clight.Efield (Clight.Ederef (Clight.Etempvar id ty_ptr) ty_deref) x xty.

Definition translate_const (c: const): Clight.expr :=
  (match c with
  | Cint i sz sg => Clight.Econst_int (Cop.cast_int_int sz sg i)
  | Clong l _ => Clight.Econst_long l
  | Cfloat f => Clight.Econst_float f
  | Csingle s => Clight.Econst_single s
  end) (cltype (type_const c)).

Definition translate_unop (op: unop): Clight.expr -> Ctypes.type -> Clight.expr :=
  match op with
  | UnaryOp cop => Clight.Eunop cop
  | CastOp _ => Clight.Ecast
  end.

Definition translate_binop (op: binop): Clight.expr -> Clight.expr -> Ctypes.type -> Clight.expr :=
  Clight.Ebinop op.

Section Translate.
  (* Variable (pro: project) (owner: class) (caller: method). *)
  Variable (pro: project)  (po: pou_decl).
  (** Straightforward expression translation *)
  Fixpoint gen_exp (e: exp): Clight.expr :=
    match e with
    | Var x ty =>
      deref_field self po.(pou_name) x (cltype ty)
    | Var_temp x ty =>
      Clight.Etempvar x (cltype ty)
    | Const c =>
      translate_const c
    | Unop op e ty =>
      translate_unop op (gen_exp e) (cltype ty)
    | Binop op e1 e2 ty =>
      translate_binop op (gen_exp e1) (gen_exp e2) (cltype ty)
    | Field e' x ty =>
      Clight.Efield (gen_exp e') x (cltype ty)
    end.

  Fixpoint list_type_to_typelist (tys: list Ctypes.type): Ctypes.typelist :=
    match tys with
    | [] => Ctypes.Tnil
    | ty :: tys => Ctypes.Tcons ty (list_type_to_typelist tys)
    end.

  Definition funcall  (f: ident)  (args: list Clight.expr) : Clight.statement :=
    let tys := map Clight.typeof args in
    let sig := Ctypes.Tfunction (list_type_to_typelist tys) Ctypes.Tvoid AST.cc_default in
    Clight.Scall None (Clight.Evar f sig) args.




  Definition translate_param '((y, t): ident * type): ident * Ctypes.type := (y, cltype t).

  Fixpoint translate_stmt (s: stmt) : Clight.statement :=
    match s with
    | Assign ex e =>
      (match ex with 
      | Var _ _ | Field _ _ _ =>
        Clight.Sassign (gen_exp ex) (gen_exp e)
      | Var_temp id _ =>
        Clight.Sset id (gen_exp e)
      | _ =>
        Clight.Sskip
      end)
    (* | Ifte e s1 s2 =>
      Clight.Sifthenelse (gen_exp e) (translate_stmt s1) (translate_stmt s2) *)
    | Comp s1 s2 =>
      Clight.Ssequence (translate_stmt s1) (translate_stmt s2)
    (* | Call ys po o f es =>
      binded_funcall ys po o f (map gen_exp es) *)
    (* | Call  =>
    (* (prefix ID_EXEC p_name) *)
      funcall  .
    | Reset _ _ =>
    (* (prefix ID_RESET p_name) *)
      Clight.Sskip *)
    | _ => Clight.Sskip
    end.

End Translate.

Section Gen.
Variable (pro: project).
Definition fundef
           (ins vars temps: list (ident * Ctypes.type))
           (ty: Ctypes.type) (body: Clight.statement)
  : AST.globdef Clight.fundef Ctypes.type :=
  let f := Clight.mkfunction ty AST.cc_default ins vars temps body in
  @AST.Gfun Clight.fundef Ctypes.type (Ctypes.Internal f).

  Definition mk_members (id_ty : (ident * type) ): ident * Ctypes.type :=
    let (id , ty) :=  id_ty in
    (id , cltype ty).
   Definition mk_members_all(p_decl: pou_decl):list (ident * Ctypes.type) :=
    (map mk_members  p_decl.(pou_vars)) ++ (map mk_members  p_decl.(pou_temps) ) .
  Definition gen_pou_struct (p_decl: pou_decl)
  :  (Ctypes.composite_definition) :=
  (*define the data struct*)
  let _members := mk_members_all  p_decl  in
  Ctypes.Composite (pou_name p_decl) Ctypes.Struct _members Ctypes.noattr .

  Definition exp_pou_reset_function (p_decl : pou_decl) : Clight.expr :=
    let p_name := p_decl.(pou_name) in 
    let sig := Ctypes.Tfunction (Ctypes.Tcons  (type_of_inst_p p_name)  Ctypes.Tnil)  Ctypes.Tvoid AST.cc_default in
    Clight.Evar (prefix ID_RESET p_name) sig.

  (* Definition mk_resets (p_decl : pou_decl)(id_vdecl : (ident * var_decl) ): Clight.statement :=
    let (id , vdecl) :=  id_vdecl in
    match vdecl with 
    | v_decl ty e =>  assign p_decl id (cltype (typeof e)) (gen_exp p_decl e)

    | var_fbd_decl fbd_id le =>  
      match find_pou_decl fbd_id pro with 
        | None =>
          Clight.Sskip
        | Some fbd_decl =>
          (* (Clight.Ederef (Clight.Etempvar id ty_ptr) ty_deref) *)
          let fbd := deref_field self p_decl.(pou_name) fbd_id (type_of_inst fbd_id) in 
          let fbd_ptr := Clight.Eaddrof fbd               (type_of_inst_p fbd_id) in 
          Clight.Scall None (exp_pou_reset_function fbd_decl) (fbd_ptr::nil)
        end
    end.

   Fixpoint mk_reset_body(p_decl: pou_decl)(id_vdecl_list : list(ident * var_decl) )
   :  Clight.statement :=
   match id_vdecl_list with
     | nil => (Clight.Sskip)
     | id_vdecl :: l =>
        let s_rec := (mk_reset_body p_decl l) in
       (Clight.Ssequence (mk_resets p_decl id_vdecl) s_rec)
   end. *)
 

  Definition gen_pou_fun_reset(p_decl: pou_decl)
  :  (ident * AST.globdef Clight.fundef Ctypes.type) :=
  let p_name := p_decl.(pou_name)  in 
  let _reset_fun_id := (prefix ID_RESET p_name) in
  let reset_body :=  (translate_stmt p_decl p_decl.(pou_reset)) in 
  let reset_fun := fundef ([(self ,  (type_of_inst_p p_name) )]) [] [] Ctypes.Tvoid reset_body   in
   (_reset_fun_id , reset_fun ).

   Definition gen_pou_fun_exec (p_decl: pou_decl)
  :  (ident * AST.globdef Clight.fundef Ctypes.type) :=
  let p_name := p_decl.(pou_name)  in 
  let _exec_fun_id := (prefix ID_EXEC p_name) in
  let exec_fun_body := (translate_stmt p_decl p_decl.(pou_body)) in                  
  let exec_fun := fundef ([ (self ,  (type_of_inst_p p_name)) ]) [] [] Ctypes.Tvoid  exec_fun_body  in
   (_exec_fun_id,exec_fun).
  
  
  Definition gen_pou (p_decl: pou_decl)
  :  list Ctypes.composite_definition * list (ident * AST.globdef Clight.fundef Ctypes.type) :=
  let composite_definition := gen_pou_struct p_decl in
  let (_reset_fun_id , reset_fun ) := gen_pou_fun_reset p_decl in
  let (_exec_fun_id,exec_fun) := gen_pou_fun_exec p_decl in 
   ([composite_definition],[(_reset_fun_id , reset_fun );(_exec_fun_id,exec_fun)]).
  
   End Gen.


  Definition myPOU_input :=   ((1%positive, _INT )
  ::(2%positive, _INT   )::nil).
  
  Check myPOU_input.
  Axiom H1: (NoDupMembers myPOU_input).
  Axiom H2: (Forall ValidId  myPOU_input).
  Definition myPOU_decl : pou_decl := mk_pou
  self
  myPOU_input (* pou_in *)
  nil
  (Assign  (Var 1%positive _INT) (Var 2%positive _INT))
  (Skip)
  H1 
  H2
  .
  Definition myProject :=  (myPOU_decl::nil) .

(*********************************************)


Definition build_composite_env' (types: list Ctypes.composite_definition) :
  res { ce | Ctypes.build_composite_env types = OK ce }.
Proof.
  destruct (Ctypes.build_composite_env types) as [ce|msg].
  - left. exists ce; auto.
  - right. exact msg.
Defined.

Definition check_size (env: Ctypes.composite_env) (id: AST.ident) :=
  match env ! id with
  | Some co =>
      if (Ctypes.co_sizeof co) <=? Ptrofs.max_unsigned
      then OK tt
      else Error [MSG "ObcToClight: structure is too big: '"; CTX id; MSG "'." ]
  | None =>
      Error [MSG "ObcToClight: structure is undefined: '"; CTX id; MSG "'." ]
  end.
Fixpoint check_size_env (env: Ctypes.composite_env) (types: list Ctypes.composite_definition)
  : res unit :=
  match types with
  | nil => OK tt
  | Ctypes.Composite id _ _ _ :: types =>
      do _ <- check_size env id;
      check_size_env env types
  end.

Definition vardef (env: Ctypes.composite_env) (volatile: bool) (x: ident * Ctypes.type)
  : ident * AST.globdef Clight.fundef Ctypes.type :=
  let (x, ty) := x in
  let ty' := Ctypes.merge_attributes ty (Ctypes.mk_attr volatile None) in
  (x, @AST.Gvar Clight.fundef _
                (AST.mkglobvar ty' [AST.Init_space (Ctypes.sizeof env ty')] false volatile)).

Definition make_program'
           (types: list Ctypes.composite_definition)
           (gvars gvars_vol: list (ident * Ctypes.type))
           (defs: list (ident * AST.globdef Clight.fundef Ctypes.type))
           (public: list ident)
           (main: ident) : res Clight.program :=
  match build_composite_env' types with
  | OK (exist ce P) =>
    do _ <- check_size_env ce types;
      OK {| Ctypes.prog_defs := map (vardef ce false) gvars ++
                                map (vardef ce true) gvars_vol ++
                                defs;
            Ctypes.prog_public := public;
            Ctypes.prog_main := main;
            Ctypes.prog_types := types;
            Ctypes.prog_comp_env := ce;
            Ctypes.prog_comp_env_eq := P |}
  | Error msg => Error msg
  end.
Definition translate (pro: project): res Clight.program :=
        let cs := map (gen_pou ) pro in
        let (structs, funs) := split cs in
        make_program' (concat structs)
                      []
                      []
                      (concat funs)
                      []
                      main_proved_id
  .