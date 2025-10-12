From compcert Require Import lib.Integers.
From compcert Require Import lib.Floats.
From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
Require Import ST_Operators.
From Velus Require Import Ident.
From Velus Require Import VelusMemory.

From compcert Require common.Values.
From compcert Require cfrontend.Cop.
From compcert Require cfrontend.Ctypes.
From compcert Require cfrontend.Ctyping.
From compcert Require common.Memory.
From compcert Require common.Memdata.
From compcert Require lib.Maps.
From Coq Require Import String.
From Coq Require Import ZArith.BinInt.
From Coq Require Import List.

Open Scope bool_scope.
(* ST_Interface avec CompCert *)

Hint Resolve Z.divide_refl.

Definition empty_composite_env : Ctypes.composite_env := (Maps.PTree.empty _).

Module Export Op <: ST_OPERATORS.
  Definition val: Type := Values.val.
  Definition not_ptr(v:val) :  Prop :=
    match v with 
    | Values.Vptr _ _ => False
    | _  => True
    end.

  Lemma not_ptr_forall : 
  forall v b ofs,
    not_ptr v ->
    v <> Values.Vptr b ofs.
  Proof.
    intros.
    destruct v;eauto;unfold not; intros H1; inversion H1.
  Qed.
  Hint Resolve not_ptr_forall.

  Inductive type' : Type :=
  | Tint:   Ctypes.intsize -> Ctypes.signedness -> type'
  | Tlong:  Ctypes.signedness -> type'
  | Tfloat: Ctypes.floatsize -> type'
  | Tinst  : ident            -> type'
  .

  Definition type := type'.

  Inductive implicit_cast'(ty1 : type)(ty2 : type) : Prop :=
  | implicit_cast0:
    ty1 = ty2 ->
    implicit_cast' ty1 ty2
  .

  Definition implicit_cast1(ty1 : type)(ty2 : type) : bool :=
    match ty1 ,ty2 with 
    | Tint Ctypes.IBool Ctypes.Signed, Tint Ctypes.IBool Ctypes.Signed => true
    | Tint Ctypes.IBool Ctypes.Unsigned, Tint Ctypes.IBool Ctypes.Unsigned => true

    | Tint Ctypes.I8 Ctypes.Signed, Tint Ctypes.I8 Ctypes.Signed => true
    | Tint Ctypes.I8 Ctypes.Signed, Tint Ctypes.I16 Ctypes.Signed => true
    | Tint Ctypes.I8 Ctypes.Signed, Tint Ctypes.I32 Ctypes.Signed => true
    | Tint Ctypes.I8 Ctypes.Signed, Tlong Ctypes.Signed => true
    | Tint Ctypes.I8 Ctypes.Signed, Tfloat Ctypes.F32 => true
    | Tint Ctypes.I8 Ctypes.Signed, Tfloat  Ctypes.F64 => true

    | Tint Ctypes.I16 Ctypes.Signed, Tint Ctypes.I16 Ctypes.Signed => true
    | Tint Ctypes.I16 Ctypes.Signed, Tint Ctypes.I32 Ctypes.Signed => true
    | Tint Ctypes.I16 Ctypes.Signed, Tlong Ctypes.Signed => true
    | Tint Ctypes.I16 Ctypes.Signed, Tfloat Ctypes.F32 => true
    | Tint Ctypes.I16 Ctypes.Signed, Tfloat  Ctypes.F64 => true

    | Tint Ctypes.I32 Ctypes.Signed, Tint Ctypes.I32 Ctypes.Signed => true
    | Tint Ctypes.I32 Ctypes.Signed, Tlong Ctypes.Signed => true
    | Tint Ctypes.I32 Ctypes.Signed, Tfloat  Ctypes.F64 => true

    | Tlong Ctypes.Signed, Tlong Ctypes.Signed => true

    | Tint Ctypes.I8 Ctypes.Unsigned, Tint Ctypes.I8 Ctypes.Unsigned => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tint Ctypes.I16 Ctypes.Unsigned => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tint Ctypes.I32 Ctypes.Unsigned => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tfloat Ctypes.F32 => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tint Ctypes.I32 Ctypes.Signed => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tlong Ctypes.Unsigned => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tfloat Ctypes.F64 => true
    | Tint Ctypes.I8 Ctypes.Unsigned, Tlong Ctypes.Signed => true


    | Tint Ctypes.I16 Ctypes.Unsigned, Tint Ctypes.I16 Ctypes.Unsigned => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tint Ctypes.I32 Ctypes.Unsigned => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tfloat Ctypes.F32 => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tint Ctypes.I32 Ctypes.Signed => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tlong Ctypes.Unsigned => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tfloat Ctypes.F64 => true
    | Tint Ctypes.I16 Ctypes.Unsigned, Tlong Ctypes.Signed => true

    | Tint Ctypes.I32 Ctypes.Unsigned, Tint Ctypes.I32 Ctypes.Unsigned => true
    | Tint Ctypes.I32 Ctypes.Unsigned, Tlong Ctypes.Unsigned => true
    | Tint Ctypes.I32 Ctypes.Unsigned, Tfloat Ctypes.F64 => true
    | Tint Ctypes.I32 Ctypes.Unsigned, Tlong Ctypes.Signed => true


    | Tlong Ctypes.Unsigned, Tlong Ctypes.Unsigned => true

    | Tfloat Ctypes.F32, Tfloat Ctypes.F32 => true
    | Tfloat Ctypes.F32, Tfloat Ctypes.F64 => true

    | Tfloat Ctypes.F64, Tfloat Ctypes.F64 => true


    | _,_ => false
    end
    .  


  Definition implicit_cast (ty1 : type)(ty2 : type) :Prop := implicit_cast1 ty1 ty2 = true.
  

  Definition is_inst(ty:type) : bool :=
    match ty with 
    | Tinst _ => true
    | _ => false
    end
  .

  Lemma implicit_cast_equal:
  forall ty,
  is_inst ty = false -> 
  implicit_cast ty ty .
  Proof.
    intros.
    unfold implicit_cast.
    destruct ty.
    + destruct i,s; eauto.
    + destruct s;eauto.
    + destruct f;eauto.
    + inv H.
  Qed.


  Definition get_pou_name(ty:type) : option ident :=
    match ty with 
    | Tinst id => Some id
    | _ => None
    end
  .
  
  Definition cltype (ty: type) : Ctypes.type :=
    match ty with
    | Tint sz sg => Ctypes.Tint sz sg Ctypes.noattr
    | Tlong sg   => Ctypes.Tlong sg (Ctypes.mk_attr false (Some (Npos 3)))
    | Tfloat sz  => Ctypes.Tfloat sz Ctypes.noattr
    | Tinst id   => Ctypes.Tstruct id Ctypes.noattr
    end.

  Definition typecl (ty: Ctypes.type) : option type :=
    match ty with
    | Ctypes.Tint sz sg attr => Some (Tint sz sg)
    | Ctypes.Tlong sg attr => Some (Tlong sg)
    | Ctypes.Tfloat sz attr => Some (Tfloat sz)
    | Ctypes.Tstruct id attr => Some(Tinst id)
    | _ => None
    end.

  Definition type_chunk (ty: type) : AST.memory_chunk :=
    match ty with
    | Tint Ctypes.I8 Ctypes.Signed    => AST.Mint8signed
    | Tint Ctypes.I8 Ctypes.Unsigned  => AST.Mint8unsigned
    | Tint Ctypes.I16 Ctypes.Signed   => AST.Mint16signed
    | Tint Ctypes.I16 Ctypes.Unsigned => AST.Mint16unsigned
    | Tint Ctypes.I32 _               => AST.Mint32
    | Tint Ctypes.IBool _             => AST.Mint8unsigned
    | Tlong _                         => AST.Mint64
    | Tfloat Ctypes.F32               => AST.Mfloat32
    | Tfloat Ctypes.F64               => AST.Mfloat64
    | _                               => AST.Many64
    end.

  (* Lemma cltype_align:
    forall gcenv ty,
      (Memdata.align_chunk (type_chunk ty) | Ctypes.alignof gcenv (cltype ty))%Z.
  Proof.
    intros; destruct ty; simpl; try rewrite align_noattr; cases;
      try (simpl; replace Archi.align_float64 with (2 * 4)%Z; auto; apply Z.divide_factor_r).
      destruct (Ctypes.co_alignof c).
  Qed. *)

  Lemma cltype_access_by_value:
  forall x ty (l:list (ident * type)),
    In (x, ty)  (filter (fun x=> negb (is_inst (snd x))) l) ->
    Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty).
  Proof.
    intros.
    destruct ty; simpl; cases; eauto.
    apply filter_In  in H.
    inv H.
    inv H1.
  Qed.
(*
  Lemma sizeof_translate_chunk:
    forall gcenv t,
      type_by_value t ->
      Ctypes.sizeof gcenv (cltype t) = Memdata.size_chunk (type_chunk t).
  Proof.
    intros; apply sizeof_by_value, cltype_access_by_value;auto.
  Qed. *)

  Definition true_val := Values.Vtrue.
  Definition false_val := Values.Vfalse.

  Lemma true_not_false_val: true_val <> false_val.
  Proof. discriminate. Qed.

  Definition bool_type : type := Tint Ctypes.IBool Ctypes.Signed.

  Inductive constant : Type :=
  | Cint: Integers.int -> Ctypes.intsize -> Ctypes.signedness -> constant
  | Clong: Integers.int64 -> Ctypes.signedness -> constant
  | Cfloat: Floats.float -> constant
  | Csingle: Floats.float32 -> constant
  .

  Definition const := constant.

  Definition type_const (c: const) : type :=
    match c with
    | Cint _ sz sg => Tint sz sg
    | Clong _ sg   => Tlong sg
    | Cfloat _     => Tfloat Ctypes.F64
    | Csingle _    => Tfloat Ctypes.F32
    end.

  Definition sem_const (c: const) : val :=
    match c with
    | Cint i sz sg => Values.Vint (Cop.cast_int_int sz sg i)
    | Clong i sg   => Values.Vlong i
    | Cfloat f     => Values.Vfloat f
    | Csingle f    => Values.Vsingle f
    end.

  Definition sem_val_cast(v: val) (ty1 ty2: type) : option val := 
    match ty1 with 
    | Tinst _ => None
    | t1 => 
        match ty2 with 
            | Tinst _ => None
            | t2 => Cop.sem_cast v (cltype t1) (cltype t2) Memory.Mem.empty
        end
    end. 
  

  Lemma sem_val_cast_no_inst:
  forall v ty1 ty2 v1,
  sem_val_cast v ty1 ty2 = Some v1 ->
  is_inst ty1 = false /\
  is_inst ty2 = false.
  Proof.
  intros.
  unfold sem_val_cast in H.
  destruct ty1,ty2;eauto; try discriminate.
  Qed.
(* 
  Definition init_type (ty: type) : const :=
    match ty with
    | Tint sz sg => Cint Integers.Int.zero sz sg
    | Tlong sg   => Clong Integers.Int64.zero sg
    | Tfloat Ctypes.F64 => Cfloat Floats.Float.zero
    | Tfloat Ctypes.F32 => Csingle Floats.Float32.zero
    | _ =>  Cundef
    end. *)

  Inductive unop' : Type :=
  | UnaryOp: Cop.unary_operation -> unop'
  | CastOp:  type -> unop'.

  Definition unop := unop'.
  Definition binop := Cop.binary_operation.

  Definition sem_unop (uop: unop) (v: val) (ty: type) : option val :=
    match uop with
    | UnaryOp op => Cop.sem_unary_operation op v (cltype ty) Memory.Mem.empty
    | CastOp ty' => Cop.sem_cast v (cltype ty) (cltype ty') Memory.Mem.empty
    end.

  Definition sem_binop (op: binop) (v1: val) (ty1: type)
                                   (v2: val) (ty2: type) : option val :=
    Cop.sem_binary_operation
      empty_composite_env op v1 (cltype ty1) v2 (cltype ty2) Memory.Mem.empty.

  Definition is_bool_type (ty: type) : bool :=
    match ty with
    | Tint Ctypes.IBool sg => true
    | _ => false
    end.

  Definition unop_always_returns_bool (op: Cop.unary_operation) : bool :=
    match op with
    | Cop.Onotbool => true
    | _            => false
    end.

  Definition type_unop (uop: unop) (ty: type) : option type :=
    match uop with
    | UnaryOp op => if unop_always_returns_bool op then Some bool_type
                    else match Ctyping.type_unop op (cltype ty) with
                         | Errors.OK ty' => typecl ty'
                         | Errors.Error _ => None
                         end
    | CastOp ty' => match Ctyping.check_cast (cltype ty) (cltype ty') with
                    | Errors.OK _ => Some ty'
                    | Errors.Error _ => None
                    end
    end.

  Definition binop_always_returns_bool (op: binop) : bool :=
    match op with
    | Cop.Oeq  => true
    | Cop.One  => true
    | Cop.Olt  => true
    | Cop.Ogt  => true
    | Cop.Ole  => true
    | Cop.Oge  => true
    | _        => false
    end.

  Definition is_bool_binop (op: binop) : bool :=
    match op with
    | Cop.Oand => true
    | Cop.Oor  => true
    | Cop.Oxor => true
    | _        => false
    end.

  Open Scope bool.

  Definition type_binop (op: binop) (ty1 ty2: type) : option type :=
    if binop_always_returns_bool op
       || (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2))
    then Some bool_type
    else match Ctyping.type_binop op (cltype ty1) (cltype ty2) with
         | Errors.OK ty' => typecl ty'
         | Errors.Error _ => None
         end.

 
  Inductive wt_val' : val -> type -> Prop :=
  | wt_val_int:
      forall n sz sg,
        Ctyping.wt_int n sz sg ->
        (sz = Ctypes.IBool -> (n = Int.zero \/ n = Int.one)) ->
        wt_val' (Values.Vint n) (Tint sz sg)
  | wt_val_long:
      forall n sg,
        wt_val' (Values.Vlong n) (Tlong sg)
  | wt_val_float:
      forall f,
        wt_val' (Values.Vfloat f) (Tfloat Ctypes.F64)
  | wt_val_single:
      forall f,
        wt_val' (Values.Vsingle f) (Tfloat Ctypes.F32)

  .

  Definition wt_val : val -> type -> Prop := wt_val'.

  Hint Unfold wt_val.
  Hint Constructors wt_val'.


  Lemma get_pou_name_inst : 
  forall t id,
  get_pou_name t = Some id -> 
  is_inst t = true.
  Proof.
  intros.
  unfold get_pou_name in H.
  destruct t; inv H.
  eauto.
  Qed.

  Lemma wt_val_const:
    forall c, wt_val (sem_const c) (type_const c).
  Proof.
    destruct c;try constructor.
    + apply Ctyping.pres_cast_int_int.
    + intro; subst; simpl.
      destruct (Int.eq i Int.zero); auto.
  Qed.

  Lemma implicit_cast_keep_value:
    forall ty1 ty2 v v2 m ,
      implicit_cast ty1 ty2 ->
      sem_val_cast v ty1 ty2 = Some v2 ->
      wt_val v ty1 ->
      (*[Vundef]*)
      (* v <> Values.Vundef ->  *)
      Cop.sem_cast v (cltype ty1) (cltype ty2) m = Some v2.
  Proof.
    intros.
    unfold sem_val_cast  in H0.
    destruct ty1,ty2; try discriminate;eauto.
    destruct i,s,i0,s0; eauto.
    destruct i,s,f;eauto.
    destruct s,i,s0; try discriminate;eauto.
    destruct s,f; try discriminate;eauto.
    destruct s,i,f; try discriminate;eauto.
    destruct f,s; try discriminate;eauto.
    destruct f,f0; try discriminate;eauto.
  Qed. 


    Lemma sem_val_cast_type_same:
    forall v ty,
    is_inst ty = false ->
    wt_val v ty ->
    sem_val_cast v ty ty = Some v.
    Proof.
    intros.
    unfold sem_val_cast.
    destruct ty;simpl.
    +
    inv H0.
    eapply Cop.cast_val_casted;simpl.
    unfold Ctyping.wt_int in H4.
    econstructor.
    destruct i,s;simpl;eauto.
    assert (Hn_cases : n = Int.zero \/ n = Int.one) by eauto.
    destruct Hn_cases as [Hn_zero | Hn_one].
    rewrite Hn_zero;eauto.   
    rewrite Hn_one;eauto.   
    assert (Hn_cases : n = Int.zero \/ n = Int.one) by eauto.
    
    destruct Hn_cases as [Hn_zero | Hn_one].
    rewrite Hn_zero;eauto.   
    rewrite Hn_one;eauto. 
    +
    inv H0.
    eapply Cop.cast_val_casted;simpl.
    econstructor.
    +
    eapply Cop.cast_val_casted;simpl.
    inv H0;econstructor.
    +
      inv H0.
    Qed.

  Lemma implicit_cast_no_inst:
  forall ty1 ty2  ,
  implicit_cast ty1 ty2 ->
  is_inst ty1  =  false /\
  is_inst ty2  =  false.
  Proof.
    intros.
    inv H.
    destruct ty1; destruct ty2;eauto.
    inv H1.
    destruct i,s; try discriminate.
    destruct s,i; try discriminate.
    destruct f,i; try discriminate. 
  Qed.

  Ltac DestructCases :=
    match goal with
    | H: ?x <> ?x |- _ => now contradiction H
    | _ => Ctyping.DestructCases
    end.

  Definition good_bool (v: Values.val) (ty: Ctypes.type) :=
    match ty, v with
    | Ctypes.Tint Ctypes.IBool sg a, Values.Vint v =>
      (v = Int.zero \/ v = Int.one)
    | _, _ => True
    end.


  Lemma good_bool_vtrue:
    forall ty,
      good_bool Values.Vtrue ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vfalse:
    forall ty,
      good_bool Values.Vfalse ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vlong:
    forall ty i,
      good_bool (Values.Vlong i) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i0; auto.
  Qed.

  Lemma good_bool_vfloat:
    forall ty f,
      good_bool (Values.Vfloat f) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_vsingle:
    forall ty f,
      good_bool (Values.Vsingle f) ty.
  Proof.
    intros; destruct ty; simpl; try destruct i; auto.
  Qed.

  Lemma good_bool_tint:
    forall v sz sg a,
      sz <> Ctypes.IBool ->
      good_bool v (Ctypes.Tint sz sg a).
  Proof.
    intros; destruct v, sz; simpl; intuition.
  Qed.

  Lemma good_bool_tlong:
    forall v sg a,
      good_bool v (Ctypes.Tlong sg a).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma good_bool_tfloat:
    forall v sz a,
      good_bool v (Ctypes.Tfloat sz a).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma good_bool_tstruct:
    forall v i,
      good_bool v (Ctypes.Tstruct i Ctypes.noattr).
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Lemma good_bool_tvoid:
    forall v,
      good_bool v Ctypes.Tvoid.
  Proof.
    intros; destruct v; simpl; auto.
  Qed.

  Local Hint Immediate good_bool_vtrue good_bool_vfalse good_bool_vlong
        good_bool_vfloat good_bool_vsingle good_bool_tlong
        good_bool_tfloat good_bool_tstruct good_bool_tvoid.

  Lemma good_bool_not_bool:
    forall v ty,
      (forall sg a, ty <> Ctypes.Tint Ctypes.IBool sg a) ->
      good_bool v ty.
  Proof.
    intros v ty Hty.
    destruct ty; simpl; eauto.
    destruct i, v; auto.
    now contradiction (Hty s a).
  Qed.

  Local Hint Resolve good_bool_not_bool.

  Opaque good_bool.

  Lemma good_bool_zero_or_one:
    forall i sz sg a,
      good_bool (Values.Vint i) (Ctypes.Tint sz sg a) ->
      sz = Ctypes.IBool ->
      i = Int.zero \/ i = Int.one.
  Proof.
    intros * Hgb Hsz; subst; inversion_clear Hgb; auto.
  Qed.

  Local Hint Resolve good_bool_zero_or_one.

  Lemma wt_val_Vfalse_bool_type:
    wt_val (Values.Vfalse) bool_type.
  Proof.
    constructor; unfold Ctyping.wt_int; [now vm_compute|intuition].
  Qed.

  Lemma wt_val_Vtrue_bool_type:
    wt_val (Values.Vtrue) bool_type.
  Proof.
    constructor; unfold Ctyping.wt_int; [now vm_compute|intuition].
  Qed.

  Local Hint Resolve wt_val_Vfalse_bool_type wt_val_Vtrue_bool_type.

  Lemma wt_val_of_bool_bool_type:
    forall v,
      wt_val (Values.Val.of_bool v) bool_type.
  Proof.
    destruct v; simpl; auto.
  Qed.

  Local Hint Resolve wt_val_of_bool_bool_type.

  Lemma typecl_wt_val_wt_val:
    forall cty ty v,
      typecl cty = Some ty ->
      Ctyping.wt_val v cty ->
      (*[Vundef]*)
      v <> Values.Vundef ->
      (forall b ofs, v <> Values.Vptr b ofs) ->
      good_bool v cty ->
      wt_val v ty.
  Proof.
    (* intros * Htcl Hcty Hnun Hnptr Hgb. *)
    intros * Htcl Hcty Hnptr Hgb.
    destruct cty;
      simpl in *;
      destruct v;
      DestructCases;
      inversion Hcty;
      subst;
      eauto.

    (* exfalso. inversion Hnptr. *)

    (* [Vundef] *)
    exfalso; now eapply Hgb.
    exfalso; now eapply Hgb.
    exfalso; now eapply Hgb.
    Qed.

  Lemma wt_val_not_vptr:
    forall v ty,
      wt_val v ty ->
      (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros * Hwt.
    destruct ty; inversion Hwt; subst;
       try (discriminate); try (contradiction);auto.
  Qed.

  Lemma wt_val_wt_val_cltype:
    forall v ty,
      wt_val v ty ->
      Ctyping.wt_val v (cltype ty).
  Proof.
    intros * Hwt.
    destruct ty; inversion_clear Hwt;
    eauto using Ctyping.wt_val.
  Qed.

  Lemma is_bool_type_true:
    forall ty,
      is_bool_type ty = true ->
      exists sg, ty = Tint Ctypes.IBool sg.
  Proof.
    destruct ty; try destruct i, s; simpl; intuition.
    - exists Ctypes.Signed; auto.
    - exists Ctypes.Unsigned; auto.
  Qed.



  Ltac GoalMatchMatch :=
    repeat match goal with
           | |- match match ?x with _ => _ end with _ => _ end = _ =>
             destruct x
           end; auto.



  Lemma wt_val_cltype_wt_val:
  forall v ty,
  Ctyping.wt_val v (cltype ty ) ->
  (forall f,ty <> Tint Ctypes.IBool f) ->
  (forall b ofs, v <> Values.Vptr b ofs) ->
  v <> Values.Vundef ->
  wt_val v ty
  .
  Proof.
    intros.
    destruct ty;simpl in H.
    -
      inv H; try congruence.
      econstructor;eauto.
      intros.
      rewrite H in H0.
      specialize (H0 s).
      contradiction. 
    - 
      inv H; try congruence.
      econstructor.
    - 
    inv H; try congruence.
      econstructor. econstructor.
    - inv H; try congruence.
  Qed.
  

Ltac solve_typing_goal A1:=
  eapply wt_val_cltype_wt_val; eauto;
  try discriminate;
  eauto;
  eapply Ctyping.pres_sem_cast in A1; eauto.

  Lemma pres_sem_cast':
    forall ty1 ty2 v1 v2  ,
      wt_val v1 ty1 -> 
      implicit_cast ty1 ty2  ->
      sem_val_cast v1 ty1 ty2 = Some v2 -> 
      wt_val v2 ty2.
  Proof.
    intros.
    unfold sem_val_cast  in H0.
    
    assert (A1: Ctyping.wt_val v1 (cltype ty1)).
    {
      eapply wt_val_wt_val_cltype in H;eauto. 
    }
    assert (A2 :forall x, ty1 <>  Tinst x ).
    {
      inv H;discriminate.
    }
    assert(A3 : Cop.sem_cast v1 (cltype ty1) (cltype ty2) Memory.Mem.empty = Some v2).
    {
      destruct ty1,ty2;eauto; try congruence.
    }

    assert (V1: forall (b : Values.block) (ofs : ptrofs), v2 <> Values.Vptr b ofs).
    {
      eapply Cop.cast_val_is_casted in A3.
      inv A3;try discriminate.
      -
      destruct ty2; simpl in H4; try congruence.
      - unfold sem_val_cast in H1.
        unfold Cop.sem_cast in H1;simpl in *.
        destruct (Cop.classify_cast (cltype ty1) (cltype ty2)) eqn:CAST;
        destruct v1; destruct ty1,ty2; try discriminate; try inv H; try discriminate.
        - destruct ty2; simpl in H4; try congruence.
        destruct ty1; inv H0. 
        destruct i0,s; try congruence.
        destruct s; try discriminate.
        destruct f; try discriminate.
      -  destruct ty2; simpl in H4; try congruence.
      -  destruct ty2; simpl in H4; try congruence. 
    }
    assert (V2: v2 <> Values.Vundef).
    {
      eapply Cop.cast_val_is_casted in A3.
      inv A3;try discriminate.
      destruct ty2; simpl in H4; try congruence.
    }
    destruct ty2. 
    + 
      destruct i.
      solve_typing_goal A1.
      solve_typing_goal A1.
      solve_typing_goal A1.
      eapply Ctyping.pres_sem_cast in A1; eauto.
      inv A1; try congruence.
      -
        econstructor;eauto.
        intros.
        unfold implicit_cast in H0.
        unfold implicit_cast1 in H0.
        destruct ty1;try congruence.
        destruct i,s0,s ;try congruence.
        inv H.
        apply H8 in H2.
        unfold Cop.sem_cast in A3.
        simpl in A3.
        inv A3. 
        inv H2.
        -- rewrite  Int.eq_true. eauto.
        -- rewrite  Int.eq_false; eauto.
           discriminate.
        -- destruct v1; inv H.
           inv H1.
           destruct (Int.eq i Int.zero) eqn:eq;eauto.
        -- destruct s0; try congruence.
        -- destruct f; try congruence.    
    + solve_typing_goal A1.
    + solve_typing_goal A1.
    + solve_typing_goal A1.
  Qed.


  Lemma pres_sem_unop:
    forall op ty1 ty v1 v,
      type_unop op ty1 = Some ty ->
      sem_unop op v1 ty1 = Some v ->
      wt_val v1 ty1 ->
      wt_val v ty.
  Proof.
    intros *   Htop Hsop Hv .
    (* pose proof (wt_val_not_vptr _ _ Hv1) as [Hnun Hnptr]. *)
    pose proof (wt_val_not_vptr _ _ Hv ) as Hnptr.
    unfold type_unop, sem_unop in *.
    destruct op as [uop|].
    - (* UnaryOp *)
      destruct (unop_always_returns_bool uop) eqn:Huop.
      + destruct uop; try discriminate Huop.
        inv Htop; intros; subst.
        simpl in Hsop.
        unfold Cop.sem_notbool, Cop.classify_bool, Coqlib.option_map in Hsop;
          DestructCases; auto.
      + apply wt_val_wt_val_cltype in Hv.
        destruct (Ctyping.type_unop uop (cltype ty1)) as [cty|] eqn:Hok;
          [|discriminate].
        assert (Hok':=Hok).
        apply Ctyping.pres_sem_unop with (2:=Hsop) (3:=Hv) in Hok;
          DestructCases.
        cut (v <> Values.Vundef
             /\ (forall b ofs, v <> Values.Vptr b ofs)
             /\ good_bool v cty).
        { destruct 1 as (Hnun' & Hnptr' & Hgb). eauto using typecl_wt_val_wt_val. }
        destruct uop; simpl in *.
        * clear Hok'. rewrite Cop.notbool_bool_val in Hsop.
          DestructCases. destruct b; repeat split; try discriminate; auto.
        * unfold Cop.sem_notint in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_neg in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
        * unfold Cop.sem_absfloat in Hsop.
          destruct v1; DestructCases; repeat split; try discriminate; auto.
    - (* CastOp *)
    (* rewrite check_cltype_cast in Htop. *)
    (* injection Htop; intro; subst. *)
    (* destruct ty1;destruct t. *)

    destruct (Ctyping.check_cast (cltype ty1) (cltype t)) ; inv Htop.
    assert(Hv': wt_val v1 ty1) by eauto.
    apply wt_val_wt_val_cltype in Hv.
    pose proof (Ctyping.pres_sem_cast _ _ _ _ _ Hv Hsop).
    eapply typecl_wt_val_wt_val with (2:=H).
    destruct ty; now simpl.
    + 
    (* result cannot be Vundef *)
    
    unfold Cop.sem_cast, Cop.classify_cast in Hsop.
    destruct Hv; DestructCases; try discriminate.
    inv Hv'.
    inv Hv' ; intros HH; discriminate HH.
    
  + (* result cannot be Vptr *)
    unfold Cop.sem_cast, Cop.classify_cast in Hsop.
    intros b ofs.
    specialize (Hnptr b ofs).
    destruct Hv; DestructCases; try discriminate; auto.
  + (* booleans must be zero or one *)
    destruct ty; simpl; auto.
    destruct i; try now (apply good_bool_tint; discriminate).
    unfold Cop.sem_cast in Hsop.
    simpl in Hsop.
    DestructCases;
      try match goal with |- context [if ?x then _ else _] => destruct x end;
      simpl; auto.
  Qed.
  Ltac DestructCasesGoal :=
    match goal with
    | [ |- match ?x with _ => _ end = _]  => try(destruct x eqn:?);auto; DestructCasesGoal
    | [ |- match match ?x with _ => _ end with _ => _ end = _ ] => try(destruct x eqn:?); DestructCases
    | _ => idtac
    end.
  Lemma sem_cast_same:
    forall m v t,
      wt_val v t ->
      v <> Values.Vundef ->
      Cop.sem_cast v (cltype t) (cltype t) m = Some v
      .
  Proof.
  intros * WTv EQ.
  inv WTv.
  +   
  unfold Cop.sem_cast,Cop.classify_cast .
  unfold Ctyping.wt_int in H.   
  destruct sz,sg,Archi.ptr64;simpl;
  auto;
  try(rewrite H ;auto);
  destruct H0;auto;rewrite H0; auto.
  + 
  apply Cop.cast_val_casted;try (constructor).
  +
  apply Cop.cast_val_casted;try (constructor).
  +
  apply Cop.cast_val_casted;try (constructor).

  Qed.

  (* Solve goal with hypothesis of the form:
       (forall b ofs, Values.Vptr b' ofs' <> Values.Vptr b ofs) *)
  Ltac ContradictNotVptr :=
      match goal with
      | H: context [Values.Vptr ?b ?i <> Values.Vptr _ _] |- _ =>
        contradiction (H b i)
      end.

  Lemma cases_of_bool:
    forall P b,
      P Values.Vtrue ->
      P Values.Vfalse ->
      P (Values.Val.of_bool b).
  Proof.
    destruct b; auto.
  Qed.

  Lemma option_map_of_bool_true_false:
    forall e x,
      Coqlib.option_map Values.Val.of_bool e = Some x ->
      x = Values.Vtrue \/ x = Values.Vfalse.
  Proof.
    intros e x Hom.
    destruct e as [b|]; [destruct b|].
    - injection Hom; intro; subst; intuition.
    - injection Hom; intro; subst; intuition.
    - discriminate Hom.
  Qed.

  Lemma sem_cmp_not_vundef_nor_vptr:
    forall cop v1 ty1 v2 ty2 m v,
      Cop.sem_cmp cop v1 ty1 v2 ty2 m = Some v ->
      v <> Values.Vundef /\ (forall b ofs, v <> Values.Vptr b ofs).
  Proof.
    intros * H.
    unfold Cop.sem_cmp in H;
      DestructCases; split; try discriminate;
        try (apply option_map_of_bool_true_false in H;
             destruct H; subst; discriminate).
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
    + unfold Cop.sem_binarith in H; DestructCases;
        apply cases_of_bool; discriminate.
  Qed.

  Lemma classify_add_cltypes:
    forall ty1 ty2,
      Cop.classify_add (cltype ty1) (cltype ty2) = Cop.add_default.
  Proof.
    unfold Cop.classify_add, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma classify_sub_cltypes:
    forall ty1 ty2,
      Cop.classify_sub (cltype ty1) (cltype ty2) = Cop.sub_default.
  Proof.
    unfold Cop.classify_sub, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma classify_cmp_cltypes:
    forall ty1 ty2,
      Cop.classify_cmp (cltype ty1) (cltype ty2) = Cop.cmp_default.
  Proof.
    unfold Cop.classify_cmp, cltype; destruct ty1, ty2; simpl; GoalMatchMatch.
  Qed.

  Lemma sem_cmp_true_or_false:
    forall cop v1 ty1 v2 ty2 m v,
      Cop.sem_cmp cop v1 ty1 v2 ty2 m = Some v ->
      v = Values.Vtrue \/ v = Values.Vfalse.
  Proof.
    intros * Hsem.
    unfold Cop.sem_cmp, Cop.sem_binarith, Cop.cmp_ptr in Hsem.
    DestructCases;
      try repeat match goal with
                 | H:Coqlib.option_map Values.Val.of_bool ?r = Some _ |- _ =>
                   destruct r; simpl in H; try discriminate;
                     injection H; clear H; intro; subst
                 | |- context [Values.Val.of_bool ?b] => destruct b; auto
                 end.
  Qed.

  (* Boolean binary operations (&&, ||) are elaborated into Sifthenelse's. *)
  Lemma binop_never_bool:
    forall op ty1 ty2 ty,
      Ctyping.type_binop op ty1 ty2 = Errors.OK ty ->
      forall sz a, ty <> Ctypes.Tint Ctypes.IBool sz a.
  Proof.
    intros op ty1 ty2 ty Htype sz a.
    unfold Ctyping.type_binop, Ctyping.binarith_type,
           Ctyping.comparison_type, Ctyping.binarith_int_type,
           Ctyping.shift_op_type in Htype.
    DestructCases; discriminate.
  Qed.

  Lemma pres_sem_binop:
    forall op ty1 ty2 ty v1 v2 v,
      type_binop op ty1 ty2 = Some ty ->
      sem_binop op v1 ty1 v2 ty2 = Some v ->
      wt_val v1 ty1 ->
      wt_val v2 ty2 ->
      wt_val v ty.
  Proof.
    unfold type_binop, sem_binop.
    intros * Hty Hsem Hwt1 Hwt2.
    destruct (binop_always_returns_bool op) eqn:Heq1; simpl in Hty;
      [|destruct
          (is_bool_binop op && (is_bool_type ty1 && is_bool_type ty2)) eqn:Heq2];
      simpl in Hty.
    - (* Binary comparisons always return a bool (zero or one). *)
      injection Hty; intro; subst.
      destruct op; try discriminate Heq1;
        unfold Cop.sem_binary_operation in Hsem;
        destruct (sem_cmp_true_or_false _ _ _ _ _ _ _ Hsem); subst; auto.
    - (* Binary operators that are closed on bool. *)
      injection Hty; intro; subst; clear Hty.
      apply andb_prop in Heq2; destruct Heq2 as (Hbop & Heq2).
      apply andb_prop in Heq2; destruct Heq2 as (Hbty1 & Hbty2).
      destruct (is_bool_type_true _ Hbty1) as (sg1 & Hty1).
      destruct (is_bool_type_true _ Hbty2) as (sg2 & Hty2).
      subst; clear Hbty1 Hbty2 Heq1.
      destruct op; try discriminate Hbop;
        destruct v1, v2;
        inv Hwt1; inv Hwt2;
          repeat match goal with H:?x = ?x -> _ \/ _ |- _ =>
                                 destruct (H eq_refl); clear H end;
          subst;
          vm_compute in Hsem;try discriminate;
          injection Hsem; intro; subst v; auto.
    - (* Everything else. *)
      destruct (Ctyping.type_binop op (cltype ty1) (cltype ty2)) eqn:Hok;
        [|discriminate].
      pose proof (binop_never_bool _ _ _ _ Hok) as Hnbool.
      pose proof (wt_val_not_vptr _ _ Hwt1) as Hnptr1.
      pose proof (wt_val_not_vptr _ _ Hwt2) as Hnptr2.
      apply wt_val_wt_val_cltype in Hwt1.
      apply wt_val_wt_val_cltype in Hwt2.
      pose proof (Ctyping.pres_sem_binop _ _ _ _ _ _ _ _ _ Hok Hsem Hwt1 Hwt2)
        as Hwt.
      cut (v <> Values.Vundef
           /\ (forall b ofs, v <> Values.Vptr b ofs)
           /\ good_bool v t).
      { destruct 1 as (Hnun' & Hnptr' & Hgb). eauto using typecl_wt_val_wt_val. }
      destruct op; simpl in Hsem; try discriminate Heq1.
      + (* add *)
        unfold Cop.sem_add, Cop.sem_binarith in Hsem.
        rewrite classify_add_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* sub *)
        unfold Cop.sem_sub, Cop.sem_binarith in Hsem.
        rewrite classify_sub_cltypes in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* mul *)
        unfold Cop.sem_mul, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* div *)
        unfold Cop.sem_div, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* mod *)
        unfold Cop.sem_mod, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* and *)
        unfold Cop.sem_and, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* or *)
        unfold Cop.sem_or, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* xor *)
        unfold Cop.sem_xor, Cop.sem_binarith in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* shl *)
        unfold Cop.sem_shl, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
      + (* shr *)
        unfold Cop.sem_shr, Cop.sem_shift in Hsem.
        DestructCases; repeat split; try discriminate; try ContradictNotVptr; auto.
  Qed.

  Lemma val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Proof Values.Val.eq.

  Lemma type_dec   : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Ctyping.floatsize_eq
                      || apply AST.ident_eq ).
  Qed.

  Lemma const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Proof.
    decide equality; (apply Ctyping.signedness_eq
                      || apply Ctyping.intsize_eq
                      || apply Int.eq_dec
                      || apply Int64.eq_dec
                      || apply Float.eq_dec
                      || apply Float32.eq_dec).
  Qed.

  Lemma unop_dec  : forall op1 op2 : unop, {op1 = op2} + {op1 <> op2}.
  Proof.
    assert (forall (x y: Cop.unary_operation), {x=y} + {x<>y})
      by decide equality.
    decide equality.
    apply type_dec.
  Qed.

  Lemma binop_dec : forall op1 op2 : binop, {op1 = op2} + {op1 <> op2}.
  Proof.
    decide equality.
  Qed.

  Lemma sem_unary_operation_any_mem:
    forall op v ty M1 M2,
      (forall b ofs, v <> Values.Vptr b ofs) ->
      Cop.sem_unary_operation op v ty M1
      = Cop.sem_unary_operation op v ty M2.
  Proof.
    intros * Hnptr.
    destruct op, v; simpl;
      unfold Cop.sem_notbool, Cop.sem_notint, Cop.sem_neg, Cop.sem_absfloat;
      repeat match goal with
             | |- (match ?x with _ => _ end) = _ => destruct x; auto
             | _ => ContradictNotVptr
             end;
      try (now destruct ty; auto).
    specialize (Hnptr b i); contradiction.
  Qed.

  Lemma sem_cast_any_mem:
    forall v ty1 ty2 M1 M2,
      (forall b ofs, v <> Values.Vptr b ofs) ->
      Cop.sem_cast v ty1 ty2 M1 = Cop.sem_cast v ty1 ty2 M2.
  Proof.
    intros * Hnptr.
    unfold Cop.sem_cast.
    destruct (Cop.classify_cast ty1 ty2); auto.
    destruct v; auto.
    specialize (Hnptr b i); contradiction.
  Qed.

  Lemma sem_binary_operation_any_cenv_mem:
    forall op v1 ty1 v2 ty2 M1 M2 cenv1 cenv2,
      (forall b ofs, v1 <> Values.Vptr b ofs) ->
      (forall b ofs, v2 <> Values.Vptr b ofs) ->
      Cop.sem_binary_operation cenv1 op v1 (cltype ty1) v2 (cltype ty2) M1
      = Cop.sem_binary_operation cenv2 op v1 (cltype ty1) v2 (cltype ty2) M2.
  Proof.
    intros * Hnptr1 Hnptr2.
    destruct op; simpl;
      unfold Cop.sem_add, Cop.sem_sub, Cop.sem_mul, Cop.sem_div, Cop.sem_mod,
             Cop.sem_and, Cop.sem_or, Cop.sem_xor, Cop.sem_shl, Cop.sem_shr,
             Cop.sem_cmp, Cop.sem_binarith;
      try rewrite classify_add_cltypes;
      try rewrite classify_sub_cltypes;
      try rewrite classify_cmp_cltypes;
      try rewrite (sem_cast_any_mem v1 (cltype ty1) _ M1 M2 Hnptr1);
      try rewrite (sem_cast_any_mem v2 (cltype ty2) _ M1 M2 Hnptr2);
      GoalMatchMatch.
  Qed.

  (* Lemma access_mode_cltype:
    forall ty,
      Ctypes.access_mode (cltype ty) = Ctypes.By_value (type_chunk ty).
  Proof.
    destruct ty as [sz sg|sz|f].
    - destruct sz, sg; auto.
    - destruct sz; auto.
    - destruct f; auto.
  Qed. *)

  Lemma wt_val_load_result:
    forall ty v,
      wt_val v ty ->
      v = Values.Val.load_result (type_chunk ty) v.
  Proof.
    intros * Hwt.
    destruct ty as [sz sg|sz|sz|id].
    - destruct sz, sg; simpl;
        inv Hwt; auto;
        match goal with
        | H:Ctyping.wt_int _ _ _ |- _ => rewrite <-H
        end;
        try rewrite Int.sign_ext_idem;
        try rewrite Int.zero_ext_idem;
        intuition.
    - destruct sz; inv Hwt; auto.
    - destruct sz; inv Hwt; auto.
    - auto. 
  Qed.


  Open Scope string_scope.

  Definition string_of_type (ty: type) : String.string :=
    match ty with
    | Tint Ctypes.IBool sg            => "bool"
    | Tint Ctypes.I8 Ctypes.Signed    => "int8"
    | Tint Ctypes.I8 Ctypes.Unsigned  => "uint8"
    | Tint Ctypes.I16 Ctypes.Signed   => "int16"
    | Tint Ctypes.I16 Ctypes.Unsigned => "uint16"
    | Tint Ctypes.I32 Ctypes.Signed   => "int32"
    | Tint Ctypes.I32 Ctypes.Unsigned => "uint32"
    | Tlong Ctypes.Signed             => "int64"
    | Tlong Ctypes.Unsigned           => "uint64"
    | Tfloat Ctypes.F32               => "float32"
    | Tfloat Ctypes.F64               => "float64"
    | Tinst _                         => "inst"
    end.
  Definition _SINT   := Tint  Ctypes.I8  Ctypes.Signed .
  Definition _INT    := Tint  Ctypes.I16 Ctypes.Signed  .           
  Definition _DINT   := Tint  Ctypes.I32 Ctypes.Signed.
  Definition _LINT   := Tlong Ctypes.Signed .
  
  Definition _USINT   := Tint  Ctypes.I8  Ctypes.Unsigned .
  Definition _UINT    := Tint  Ctypes.I16 Ctypes.Unsigned  .           
  Definition _UDINT   := Tint  Ctypes.I32 Ctypes.Unsigned.
  Definition _ULINT   := Tlong Ctypes.Unsigned .
End Op.

Hint Resolve  cltype_access_by_value wt_val_load_result sem_cast_same.

Module OpAux := OperatorsAux Op.

Lemma val_to_bool_bool_val:
  forall v b m,
    OpAux.val_to_bool v = Some b ->
    Cop.bool_val v (cltype bool_type) m = Some b.
Proof.
  intros * Vtb.
  unfold Cop.bool_val; simpl.
  destruct b.
  - apply OpAux.val_to_bool_true' in Vtb; subst; simpl.
    rewrite Int.eq_false; auto; discriminate.
  - apply OpAux.val_to_bool_false' in Vtb; subst; simpl.
    rewrite Int.eq_true; auto.
Qed.
Hint Resolve val_to_bool_bool_val.

From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
Require Import ST.

Module ST  := ST_Fun        Ids Op OpAux.

