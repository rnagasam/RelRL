(* collision_registry.ml - Track and resolve identifier collisions
   
   This module implements automatic collision detection and renaming for generated
   identifiers, allowing WhyRel to freely rename generated identifiers without
   restricting user-defined identifiers in .rl files.
   
   Key components:
   - Collects all user-defined identifiers from the annotated program
   - Tracks generated identifiers to avoid collisions within generation
   - Provides fresh identifier generation with automatic suffixing
*)

open Why3

module StringSet = Set.Make(String)

type collision_registry = {
  mutable user_idents: StringSet.t;      (* Set of user-provided identifiers *)
  mutable generated_idents: StringSet.t; (* Set of generated identifiers *)
}

let create () = {
  user_idents = StringSet.empty;
  generated_idents = StringSet.empty;
}

(** Extract string from an ident (handles both qualified and unqualified) *)
let ident_to_string id =
  match id with
  | Ast.Id s -> s
  | Ast.Qualid (s, ss) -> String.concat "_" (s :: ss)

(** Collect all user-provided identifiers from an annotated program *)
let collect_user_identifiers (penv: Annot.penv) : StringSet.t =
  let idents = ref StringSet.empty in
  
  let add_ident (id: Ast.ident) = 
    let id_str = ident_to_string id in
    idents := StringSet.add id_str !idents
  in
  
  let rec walk_formula = function
    | Annot.Ftrue -> ()
    | Annot.Ffalse -> ()
    | Annot.Fexp e -> walk_exp e
    | Annot.Finit lbv -> walk_let_bound_value lbv
    | Annot.Fnot f -> walk_formula f
    | Annot.Fpointsto (id1, id2, e) -> add_ident id1.node; add_ident id2.node; walk_exp e
    | Annot.Farray_pointsto (id1, e1, e2) -> add_ident id1.node; walk_exp e1; walk_exp e2
    | Annot.Fsubseteq (e1, e2) -> walk_exp e1; walk_exp e2
    | Annot.Fdisjoint (e1, e2) -> walk_exp e1; walk_exp e2
    | Annot.Fmember (e1, e2) -> walk_exp e1; walk_exp e2
    | Annot.Flet (id, lb, f) -> add_ident id.node; walk_let_bind lb; walk_formula f
    | Annot.Fconn (_, f1, f2) -> walk_formula f1; walk_formula f2
    | Annot.Fquant (_, qbs, f) -> 
      List.iter (fun qb -> add_ident qb.Annot.name.node) qbs;
      walk_formula f
    | Annot.Fold (e, lbv) -> walk_exp e; walk_let_bound_value lbv
    | Annot.Ftype (e, cls) -> walk_exp e; List.iter add_ident cls
  
  and walk_exp e =
    match e.Annot.node with
    | Annot.Econst _ -> ()
    | Annot.Evar id -> add_ident id.node
    | Annot.Ebinop (_, e1, e2) -> walk_exp e1; walk_exp e2
    | Annot.Eunrop (_, e) -> walk_exp e
    | Annot.Esingleton e -> walk_exp e
    | Annot.Eimage (e, id) -> walk_exp e; add_ident id.node
    | Annot.Esubrgn (e, cname) -> walk_exp e; add_ident cname
    | Annot.Ecall (id, es) -> add_ident id.node; List.iter walk_exp es
    | Annot.Einit e -> walk_exp e
  
  and walk_let_bound_value lbv =
    match lbv.Annot.node with
    | Annot.Lloc (id1, id2) -> add_ident id1.node; add_ident id2.node
    | Annot.Larr (id, e) -> add_ident id.node; walk_exp e
    | Annot.Lexp e -> walk_exp e
  
  and walk_let_bind lb =
    walk_let_bound_value lb.Annot.node.Annot.value
  
  and walk_command = function
    | Annot.Acommand ac -> walk_atomic_command ac
    | Annot.Vardecl (id, _, _, cmd) -> add_ident id.node; walk_command cmd
    | Annot.Seq (c1, c2) -> walk_command c1; walk_command c2
    | Annot.If (e, c1, c2) -> walk_exp e; walk_command c1; walk_command c2
    | Annot.While (e, _, c) -> walk_exp e; walk_command c
    | Annot.Assume f -> walk_formula f
    | Annot.Assert f -> walk_formula f
  
  and walk_atomic_command = function
    | Annot.Skip -> ()
    | Annot.Assign (id, e) -> add_ident id.node; walk_exp e
    | Annot.Havoc id -> add_ident id.node
    | Annot.New_class (id, cname) -> add_ident id.node; add_ident cname
    | Annot.New_array (id, cname, e) -> add_ident id.node; add_ident cname; walk_exp e
    | Annot.Field_deref (id1, id2, fname) -> add_ident id1.node; add_ident id2.node; add_ident fname.node
    | Annot.Field_update (id1, fname, e) -> add_ident id1.node; add_ident fname.node; walk_exp e
    | Annot.Array_access (id1, id2, e) -> add_ident id1.node; add_ident id2.node; walk_exp e
    | Annot.Array_update (id1, e1, e2) -> add_ident id1.node; walk_exp e1; walk_exp e2
    | Annot.Call (id_opt, id2, ids) -> 
      (match id_opt with Some {node; _} -> add_ident node | None -> ());
      add_ident id2.node;
      let process_id (id_elem : Ast.ident Annot.t) = add_ident id_elem.node in
      List.iter process_id ids
  
  and walk_class_def = function
    | Annot.Class cdef ->
      add_ident cdef.Annot.class_name;
      List.iter (fun fd -> add_ident fd.Annot.field_name.node) cdef.Annot.fields
  
  and walk_meth_def mdef =
    match mdef with
    | Annot.Method (mdecl, cmd_opt) ->
      add_ident mdecl.Annot.meth_name.node;
      List.iter (fun p -> add_ident p.Annot.param_name.node) mdecl.Annot.params;
      (match cmd_opt with Some cmd -> walk_command cmd | None -> ())
  
  and walk_interface_elt = function
    | Annot.Intr_cdecl cdecl ->
      add_ident cdecl.Annot.class_name;
      List.iter (fun fd -> add_ident fd.Annot.field_name.node) cdecl.Annot.fields
    | Annot.Intr_mdecl mdecl ->
      add_ident mdecl.Annot.meth_name.node;
      List.iter (fun p -> add_ident p.Annot.param_name.node) mdecl.Annot.params
    | Annot.Intr_vdecl (_, id, _) ->
      add_ident id.node
    | Annot.Intr_boundary boundary ->
      List.iter (fun eff_desc ->
        match eff_desc.Annot.node with
        | Annot.Effvar id -> add_ident id.node
        | Annot.Effimg (e, id) -> walk_exp e; add_ident id.node
      ) boundary
    | Annot.Intr_datagroup dg -> List.iter add_ident dg
    | Annot.Intr_formula nf ->
      add_ident nf.Annot.formula_name.node;
      let process_param (param : Ast.ident Annot.t) = add_ident param.node in
      List.iter process_param nf.Annot.params;
      walk_formula nf.Annot.body
    | Annot.Intr_import _ -> ()
    | Annot.Intr_extern ed ->
      (match ed with
       | Annot.Extern_type (id, _) -> add_ident id
       | Annot.Extern_const (id, _) -> add_ident id
       | Annot.Extern_axiom id -> add_ident id
       | Annot.Extern_lemma id -> add_ident id
       | Annot.Extern_predicate p -> add_ident p.name
       | Annot.Extern_function f -> add_ident f.name
       | Annot.Extern_bipredicate b -> add_ident b.name)
    | Annot.Intr_inductive ind ->
      add_ident ind.Annot.ind_name.node;
      let process_param (param : Ast.ident Annot.t) = add_ident param.node in
      List.iter process_param ind.Annot.ind_params;
      List.iter (fun (id, _) -> add_ident id) ind.Annot.ind_cases
  
  and walk_module_elt = function
    | Annot.Mdl_cdef cdef -> walk_class_def cdef
    | Annot.Mdl_mdef mdef -> walk_meth_def mdef
    | Annot.Mdl_vdecl (_, id, _) -> add_ident id.node
    | Annot.Mdl_datagroup (dg_name, dg_fields) ->
      add_ident dg_name;
      let process_field (field : Ast.ident Annot.t) = add_ident field.node in
      List.iter process_field dg_fields
    | Annot.Mdl_formula nf ->
      add_ident nf.Annot.formula_name.node;
      let process_param (param : Ast.ident Annot.t) = add_ident param.node in
      List.iter process_param nf.Annot.params;
      walk_formula nf.Annot.body
    | Annot.Mdl_import _ -> ()
    | Annot.Mdl_extern ed ->
      (match ed with
       | Annot.Extern_type (id, _) -> add_ident id
       | Annot.Extern_const (id, _) -> add_ident id
       | Annot.Extern_axiom id -> add_ident id
       | Annot.Extern_lemma id -> add_ident id
       | Annot.Extern_predicate p -> add_ident p.name
       | Annot.Extern_function f -> add_ident f.name
       | Annot.Extern_bipredicate b -> add_ident b.name)
    | Annot.Mdl_inductive ind ->
      add_ident ind.Annot.ind_name.node;
      let process_param (param : Ast.ident Annot.t) = add_ident param.node in
      List.iter process_param ind.Annot.ind_params;
      List.iter (fun (id, _) -> add_ident id) ind.Annot.ind_cases
  
  and walk_bimeth_def bdef =
    match bdef with
    | Annot.Bimethod (bdecl, cmd_opt) ->
      add_ident bdecl.Annot.bimeth_name;
      List.iter (fun p -> add_ident p.Annot.param_name.node) bdecl.Annot.bimeth_left_params;
      List.iter (fun p -> add_ident p.Annot.param_name.node) bdecl.Annot.bimeth_right_params;
      (match cmd_opt with Some cmd -> walk_bicommand cmd | None -> ())
  
  and walk_rformula = function
    | Annot.Rprimitive prim -> add_ident prim.name; List.iter walk_exp prim.left_args; List.iter walk_exp prim.right_args
    | Annot.Rbiequal (e1, e2) -> walk_exp e1; walk_exp e2
    | Annot.Rbiexp be -> walk_biexp be
    | Annot.Ragree (e, id) -> walk_exp e; add_ident id.node
    | Annot.Rboth f -> walk_formula f
    | Annot.Rleft f -> walk_formula f
    | Annot.Rright f -> walk_formula f
    | Annot.Rnot rf -> walk_rformula rf
    | Annot.Rconn (_, rf1, rf2) -> walk_rformula rf1; walk_rformula rf2
    | Annot.Rquant (_, (qbs1, qbs2), rf) ->
      List.iter (fun qb -> add_ident qb.Annot.name.node) qbs1;
      List.iter (fun qb -> add_ident qb.Annot.name.node) qbs2;
      walk_rformula rf
    | Annot.Rlet (left_binder, right_binder, rf) ->
      (match left_binder with Some (id, _, _) -> add_ident id.node | None -> ());
      (match right_binder with Some (id, _, _) -> add_ident id.node | None -> ());
      walk_rformula rf
    | Annot.Rlater rf -> walk_rformula rf
  
  and walk_bicommand = function
    | Annot.Bihavoc_right (id, rf) -> add_ident id.node; walk_rformula rf
    | Annot.Bisplit (c1, c2) -> walk_command c1; walk_command c2
    | Annot.Bisync ac -> walk_atomic_command ac
    | Annot.Bivardecl (vb1, vb2, bc) ->
      (match vb1 with Some (id, _, _) -> add_ident id.node | None -> ());
      (match vb2 with Some (id, _, _) -> add_ident id.node | None -> ());
      walk_bicommand bc
    | Annot.Biseq (bc1, bc2) -> walk_bicommand bc1; walk_bicommand bc2
    | Annot.Biif (e1, e2, bc1, bc2) -> walk_exp e1; walk_exp e2; walk_bicommand bc1; walk_bicommand bc2
    | Annot.Biif4 (e1, e2, fwif) ->
      walk_exp e1; walk_exp e2;
      walk_bicommand fwif.Annot.then_then;
      walk_bicommand fwif.Annot.then_else;
      walk_bicommand fwif.Annot.else_then;
      walk_bicommand fwif.Annot.else_else
    | Annot.Biwhile (e1, e2, _, bws, bc) ->
      walk_exp e1; walk_exp e2;
      (match bws.Annot.biwvariant with Some be -> walk_biexp be | None -> ());
      walk_bicommand bc
    | Annot.Biassume rf -> walk_rformula rf
    | Annot.Biassert rf -> walk_rformula rf
    | Annot.Biupdate (id1, id2) -> add_ident id1.node; add_ident id2.node
  
  and walk_biexp be =
    match be.Annot.node with
    | Annot.Biconst _ -> ()
    | Annot.Bibinop (_, be1, be2) -> walk_biexp be1; walk_biexp be2
    | Annot.Bivalue vis ->
      (match vis.Annot.node with
       | Annot.Left e -> walk_exp e
       | Annot.Right e -> walk_exp e)
  
  and walk_bimodule_elt = function
    | Annot.Bimdl_mdef mdef -> walk_bimeth_def mdef
    | Annot.Bimdl_formula bf ->
      add_ident bf.Annot.biformula_name;
      let (left_params, right_params) = bf.Annot.biparams in
      let process_param ((param : Ast.ident Annot.t), _) = add_ident param.node in
      List.iter process_param left_params;
      List.iter process_param right_params;
      walk_rformula bf.Annot.body
    | Annot.Bimdl_extern ed ->
      (match ed with
       | Annot.Extern_type (id, _) -> add_ident id
       | Annot.Extern_const (id, _) -> add_ident id
       | Annot.Extern_axiom id -> add_ident id
       | Annot.Extern_lemma id -> add_ident id
       | Annot.Extern_predicate p -> add_ident p.name
       | Annot.Extern_function f -> add_ident f.name
       | Annot.Extern_bipredicate b -> add_ident b.name)
    | Annot.Bimdl_import _ -> ()
  
  and walk_program_elt = function
    | Annot.Unary_interface idef ->
      add_ident idef.Annot.intr_name;
      List.iter walk_interface_elt idef.Annot.intr_elts
    | Annot.Unary_module mdef ->
      add_ident mdef.Annot.mdl_name;
      List.iter walk_module_elt mdef.Annot.mdl_elts
    | Annot.Relation_module bimdl ->
      add_ident bimdl.Annot.bimdl_name;
      add_ident bimdl.Annot.bimdl_left_impl;
      add_ident bimdl.Annot.bimdl_right_impl;
      List.iter walk_bimodule_elt bimdl.Annot.bimdl_elts
  in
  
  Astutil.M.iter (fun _ elt -> walk_program_elt elt) penv;
  !idents

(** Initialize registry with user identifiers from the annotated program *)
let init_with_penv registry (penv: Annot.penv) =
  registry.user_idents <- collect_user_identifiers penv

(** Generate a fresh identifier that doesn't collide with user or previously generated identifiers *)
let mk_fresh_ident registry (base_str : string) : string =
  let rec generate suffix =
    let candidate = if suffix = 0 then base_str 
                    else base_str ^ string_of_int suffix in
    if StringSet.mem candidate registry.user_idents ||
       StringSet.mem candidate registry.generated_idents
    then generate (suffix + 1)
    else candidate
  in
  let result = generate 0 in
  registry.generated_idents <- StringSet.add result registry.generated_idents;
  result
