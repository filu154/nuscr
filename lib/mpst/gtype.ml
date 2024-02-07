open! Base
open Loc
open Err
open Names
open Message

type scr_module = Syntax.scr_module

type global_protocol = Syntax.global_protocol

type rec_var =
  { rv_name: VariableName.t
  ; rv_roles: RoleName.t list
  ; rv_ty: Expr.payload_type
  ; rv_init_expr: Expr.t }
[@@deriving sexp_of, eq]

type t =
  | MessageG of message * RoleName.t * RoleName.t * t
  | MuG of TypeVariableName.t * rec_var list * t
  | TVarG of TypeVariableName.t * Expr.t list * (t Lazy.t[@sexp.opaque])
  | ChoiceG of RoleName.t * t list
  | EndG
  | CallG of RoleName.t * ProtocolName.t * RoleName.t list * t
[@@deriving sexp_of]

let rec evaluate_lazy_gtype = function
  | MessageG (m, r1, r2, g) -> MessageG (m, r1, r2, evaluate_lazy_gtype g)
  | MuG (tv, rv, g) -> MuG (tv, rv, evaluate_lazy_gtype g)
  | TVarG (tv, es, g) ->
      TVarG
        ( tv
        , es
        , (* Force evaluation, then convert back to a lazy value *)
          Lazy.from_val (Lazy.force g) )
  | ChoiceG (r, gs) -> ChoiceG (r, List.map ~f:evaluate_lazy_gtype gs)
  | EndG -> EndG
  | CallG (r, p, rs, g) -> CallG (r, p, rs, evaluate_lazy_gtype g)

type nested_global_info =
  { static_roles: RoleName.t list
  ; dynamic_roles: RoleName.t list
  ; nested_protocol_names: ProtocolName.t list
  ; gtype: t }

type nested_t = nested_global_info Map.M(ProtocolName).t

module Formatting = struct
  open! Stdlib.Format

  let pp_rec_var ppf {rv_name; rv_roles; rv_ty; rv_init_expr} =
    fprintf ppf "%s<%s>:@ %s@ =@ %s"
      (VariableName.user rv_name)
      (String.concat ~sep:", " (List.map ~f:RoleName.user rv_roles))
      (Expr.show_payload_type rv_ty)
      (Expr.show rv_init_expr)

  let show_rec_var rv =
    let buffer = Buffer.create 1024 in
    let ppf = formatter_of_buffer buffer in
    fprintf ppf "%a@?" pp_rec_var rv ;
    Buffer.contents buffer

  let rec pp ppf = function
    | MessageG (m, r1, r2, g) ->
        pp_print_string ppf (show_message m) ;
        pp_print_string ppf " from " ;
        pp_print_string ppf (RoleName.user r1) ;
        pp_print_string ppf " to " ;
        pp_print_string ppf (RoleName.user r2) ;
        pp_print_string ppf ";" ;
        pp_force_newline ppf () ;
        pp ppf g
    | MuG (n, rec_vars, g) ->
        pp_print_string ppf "rec " ;
        pp_print_string ppf (TypeVariableName.user n) ;
        pp_print_string ppf " " ;
        if not (List.is_empty rec_vars) then (
          let rec pp_recvars = function
            | [] -> ()
            | recvar :: recvars ->
                pp_rec_var ppf recvar ;
                if not (List.is_empty recvars) then pp_print_string ppf ", " ;
                pp_recvars recvars
          in
          pp_print_string ppf "[" ;
          pp_open_box ppf 2 ;
          pp_recvars rec_vars ;
          pp_close_box ppf () ;
          pp_print_string ppf "] " ) ;
        pp_print_string ppf "{" ;
        pp_force_newline ppf () ;
        pp_open_box ppf 2 ;
        pp_print_string ppf "  " ;
        pp ppf g ;
        pp_close_box ppf () ;
        pp_force_newline ppf () ;
        pp_print_string ppf "}"
    | TVarG (n, rec_exprs, _) ->
        let rec_exprs_s =
          if List.is_empty rec_exprs then ""
          else
            " ["
            ^ String.concat ~sep:", " (List.map ~f:Expr.show rec_exprs)
            ^ "]"
        in
        pp_print_string ppf "continue " ;
        pp_print_string ppf (TypeVariableName.user n) ;
        pp_print_string ppf rec_exprs_s ;
        pp_print_string ppf ";"
    | EndG -> pp_print_string ppf "(end)"
    | ChoiceG (r, gs) ->
        pp_print_string ppf "choice at " ;
        pp_print_string ppf (RoleName.user r) ;
        pp_print_string ppf " {" ;
        pp_force_newline ppf () ;
        pp_open_box ppf 2 ;
        pp_print_string ppf "  " ;
        let rec pp_choices = function
          | [] ->
              Err.violation ~here:[%here] "Choice branches must not be empty"
          | [g] ->
              pp ppf g ;
              pp_close_box ppf () ;
              pp_force_newline ppf () ;
              pp_print_string ppf "}"
          | g :: gs ->
              pp ppf g ;
              pp_close_box ppf () ;
              pp_force_newline ppf () ;
              pp_print_string ppf "} or {" ;
              pp_force_newline ppf () ;
              pp_open_box ppf 2 ;
              pp_print_string ppf "  " ;
              pp_choices gs
        in
        pp_choices gs
    | CallG (caller, proto_name, roles, g) ->
        pp_print_string ppf (RoleName.user caller) ;
        pp_print_string ppf " calls " ;
        pp_print_string ppf (ProtocolName.user proto_name) ;
        pp_print_string ppf "(" ;
        let rec pp_roles = function
          | [] -> ()
          | r :: roles ->
              pp_print_string ppf (RoleName.user r) ;
              if not (List.is_empty roles) then pp_print_string ppf "," ;
              pp_roles roles
        in
        pp_roles roles ;
        pp_print_string ppf ");" ;
        pp_force_newline ppf () ;
        pp ppf g

  let show gtype =
    let buffer = Buffer.create 1024 in
    let ppf = formatter_of_buffer buffer in
    fprintf ppf "%a@?" pp gtype ;
    Buffer.contents buffer

  let call_label caller protocol roles =
    let str_roles = List.map ~f:RoleName.user roles in
    let roles_str = String.concat ~sep:"," str_roles in
    (* Current label is a bit arbitrary - find better one? *)
    let label_str =
      sprintf "call(%s, %s(%s))" (RoleName.user caller)
        (ProtocolName.user protocol)
        roles_str
    in
    LabelName.create label_str (ProtocolName.where protocol)

  let show_nested_t (g : nested_t) =
    let show_aux ~key ~data acc =
      let {static_roles; dynamic_roles; nested_protocol_names; gtype} =
        data
      in
      let str_proto_names =
        List.map ~f:ProtocolName.user nested_protocol_names
      in
      let names_str = String.concat ~sep:", " str_proto_names in
      let proto_str =
        sprintf "protocol %s(%s) {\n\nNested Protocols: %s\n\n%s\n}"
          (ProtocolName.user key)
          (Symtable.show_roles (static_roles, dynamic_roles))
          (if String.length names_str = 0 then "-" else names_str)
          (show gtype)
      in
      proto_str :: acc
    in
    String.concat ~sep:"\n\n" (List.rev (Map.fold ~init:[] ~f:show_aux g))
end

include Formatting

let rec_var_of_syntax_rec_var rec_var =
  let open Syntax in
  let {var; roles; ty; init} = rec_var in
  let rv_ty =
    match of_syntax_payload ty with
    | PValue (_, ty) -> ty
    | _ -> assert false
  in
  {rv_name= var; rv_roles= roles; rv_ty; rv_init_expr= init}

type conv_env =
  { free_names: Set.M(TypeVariableName).t
  ; lazy_conts:
      (t * Set.M(TypeVariableName).t) Lazy.t Map.M(TypeVariableName).t
  ; unguarded_tvs: Set.M(TypeVariableName).t }

let init_conv_env =
  { free_names= Set.empty (module TypeVariableName)
  ; lazy_conts= Map.empty (module TypeVariableName)
  ; unguarded_tvs= Set.empty (module TypeVariableName) }

let of_protocol (global_protocol : Syntax.global_protocol) =
  let open Syntax in
  let {Loc.value= {roles; interactions; _}; _} = global_protocol in
  let assert_empty l =
    if not @@ List.is_empty l then
      unimpl ~here:[%here] "Non tail-recursive protocol"
  in
  let check_role r =
    if not @@ List.mem roles r ~equal:RoleName.equal then
      uerr @@ UnboundRole r
  in
  let rec conv_interactions env (interactions : global_interaction list) =
    match interactions with
    | [] -> (EndG, env.free_names)
    | {value; _} :: rest -> (
      match value with
      | MessageTransfer {message; from_role; to_roles; _} ->
          check_role from_role ;
          let init, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          let f to_role acc =
            check_role to_role ;
            if RoleName.equal from_role to_role then
              uerr
                (ReflexiveMessage
                   ( from_role
                   , RoleName.where from_role
                   , RoleName.where to_role ) ) ;
            MessageG (of_syntax_message message, from_role, to_role, acc)
          in
          (List.fold_right ~f ~init to_roles, free_names)
      | Recursion (rname, rec_vars, interactions) ->
          if Set.mem env.free_names rname then
            unimpl ~here:[%here] "Alpha convert recursion names"
          else assert_empty rest ;
          let rec lazy_cont =
            lazy
              (conv_interactions
                 { env with
                   lazy_conts=
                     Map.add_exn ~key:rname ~data:lazy_cont env.lazy_conts
                 ; unguarded_tvs= Set.add env.unguarded_tvs rname }
                 interactions )
          in
          let rec_vars =
            if Pragma.refinement_type_enabled () then
              List.map ~f:rec_var_of_syntax_rec_var rec_vars
            else []
          in
          List.iter
            ~f:(fun {rv_roles; _} -> List.iter ~f:check_role rv_roles)
            rec_vars ;
          let cont, free_names_ = Lazy.force lazy_cont in
          (* Remove degenerate recursion here *)
          if Set.mem free_names_ rname then
            (MuG (rname, rec_vars, cont), Set.remove free_names_ rname)
          else (cont, free_names_)
      | Continue (name, rec_exprs) ->
          let rec_exprs =
            if Pragma.refinement_type_enabled () then rec_exprs else []
          in
          if Set.mem env.unguarded_tvs name then
            uerr (UnguardedTypeVariable name) ;
          let cont =
            lazy (Lazy.force (Map.find_exn env.lazy_conts name) |> fst)
          in
          assert_empty rest ;
          (TVarG (name, rec_exprs, cont), Set.add env.free_names name)
      | Choice (role, interactions_list) ->
          assert_empty rest ;
          check_role role ;
          if List.length interactions_list = 1 then
            (* Remove degenerate choice *)
            let interaction = List.hd_exn interactions_list in
            conv_interactions env interaction
          else
            let conts =
              List.map ~f:(conv_interactions env) interactions_list
            in
            ( ChoiceG (role, List.map ~f:fst conts)
            , Set.union_list
                (module TypeVariableName)
                (List.map ~f:snd conts) )
      | Do (protocol, roles, _) ->
          (* This case is only reachable with NestedProtocols pragma turned on
           * *)
          assert (Pragma.nested_protocol_enabled ()) ;
          let fst_role = List.hd_exn roles in
          let cont, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          (CallG (fst_role, protocol, roles, cont), free_names)
      | Calls (caller, proto, roles, _) ->
          let cont, free_names =
            conv_interactions
              {env with unguarded_tvs= Set.empty (module TypeVariableName)}
              rest
          in
          (CallG (caller, proto, roles, cont), free_names) )
  in
  let gtype, free_names = conv_interactions init_conv_env interactions in
  match Set.choose free_names with
  | Some free_name -> uerr (UnboundRecursionName free_name)
  | None -> evaluate_lazy_gtype gtype

let rec flatten = function
  | ChoiceG (role, choices) ->
      let choices = List.map ~f:flatten choices in
      let lift = function
        | ChoiceG (role_, choices_) when RoleName.equal role role_ ->
            choices_
        | ChoiceG (role_, _choices) ->
            uerr (InconsistentNestedChoice (role, role_))
        | g -> [g]
      in
      ChoiceG (role, List.concat_map ~f:lift choices)
  | g -> g

let rec substitute g tvar g_sub =
  match g with
  | TVarG (tvar_, rec_exprs, _) when TypeVariableName.equal tvar tvar_ -> (
    match g_sub with
    | MuG (tvar__, rec_vars, g) ->
        let rec_vars =
          match
            List.map2
              ~f:(fun rec_var rec_expr ->
                {rec_var with rv_init_expr= rec_expr} )
              rec_vars rec_exprs
          with
          | Base.List.Or_unequal_lengths.Ok rec_vars -> rec_vars
          | _ -> unimpl ~here:[%here] "Error in substitution"
        in
        MuG (tvar__, rec_vars, g)
    | g_sub -> g_sub )
  | TVarG _ -> g
  | MuG (tvar_, _, _) when TypeVariableName.equal tvar tvar_ -> g
  | MuG (tvar_, rec_vars, g_) ->
      MuG (tvar_, rec_vars, substitute g_ tvar g_sub)
  | EndG -> EndG
  | MessageG (m, r1, r2, g_) -> MessageG (m, r1, r2, substitute g_ tvar g_sub)
  | ChoiceG (r, g_) ->
      ChoiceG (r, List.map ~f:(fun g__ -> substitute g__ tvar g_sub) g_)
  | CallG (caller, protocol, roles, g_) ->
      CallG (caller, protocol, roles, substitute g_ tvar g_sub)

let rec unfold = function
  | MuG (tvar, _, g_) as g -> substitute g_ tvar g
  | g -> g

let rec normalise = function
  | MessageG (m, r1, r2, g_) -> MessageG (m, r1, r2, normalise g_)
  | ChoiceG (r, g_) ->
      let g_ = List.map ~f:normalise g_ in
      flatten (ChoiceG (r, g_))
  | (EndG | TVarG _) as g -> g
  | MuG (tvar, rec_vars, g_) -> unfold (MuG (tvar, rec_vars, normalise g_))
  | CallG (caller, protocol, roles, g_) ->
      CallG (caller, protocol, roles, normalise g_)

let normalise_nested_t (nested_t : nested_t) =
  let normalise_protocol ~key ~data acc =
    let {gtype; _} = data in
    Map.add_exn acc ~key ~data:{data with gtype= normalise gtype}
  in
  Map.fold
    ~init:(Map.empty (module ProtocolName))
    ~f:normalise_protocol nested_t

let validate_refinements_exn t =
  let env =
    ( Expr.new_typing_env
    , Map.empty (module TypeVariableName)
    , Map.empty (module RoleName) )
  in
  let knowledge_add role_knowledge role variable =
    Map.update role_knowledge role ~f:(function
      | None -> Set.singleton (module VariableName) variable
      | Some s -> Set.add s variable )
  in
  let ensure_knowledge role_knowledge role e =
    let known_vars =
      Option.value
        ~default:(Set.empty (module VariableName))
        (Map.find role_knowledge role)
    in
    let free_vars = Expr.free_var e in
    let unknown_vars = Set.diff free_vars known_vars in
    if Set.is_empty unknown_vars then ()
    else uerr (UnknownVariableValue (role, Set.choose_exn unknown_vars))
  in
  let encode_progress_clause env payloads =
    let e =
      List.fold ~init:(Expr.Sexp.Atom "true")
        ~f:(fun e -> function
          | PValue (None, _) -> e
          | PValue (Some v, ty) ->
              let sort = Expr.smt_sort_of_type ty in
              let e =
                match ty with
                | Expr.PTRefined (v_, _, refinement) ->
                    if VariableName.equal v v_ then
                      Expr.Sexp.List
                        [ Expr.Sexp.Atom "and"
                        ; Expr.sexp_of_expr refinement
                        ; e ]
                    else
                      Err.violationf ~here:[%here]
                        "TODO: Handle the case where refinement and payload \
                         variables are different"
                | _ -> e
              in
              Expr.Sexp.List
                [ Expr.Sexp.Atom "exists"
                ; Expr.Sexp.List
                    [ Expr.Sexp.List
                        [ Expr.Sexp.Atom (VariableName.user v)
                        ; Expr.Sexp.Atom sort ] ]
                ; e ]
          | PDelegate _ -> (* Not supported *) e )
        payloads
    in
    let env =
      Expr.add_assert_s_expr (Expr.Sexp.List [Expr.Sexp.Atom "not"; e]) env
    in
    env
  in
  let ensure_progress env gs =
    let tyenv, _, _ = env in
    let encoded = Expr.encode_env tyenv in
    let rec gather_first_message = function
      | MessageG (m, _, _, _) -> [m.payload]
      | ChoiceG (_, gs) -> List.concat_map ~f:gather_first_message gs
      | MuG (_, _, g) -> gather_first_message g
      | TVarG (_, _, g) -> gather_first_message (Lazy.force g)
      | EndG -> []
      | CallG _ -> (* Not supported *) []
    in
    let first_messages = List.concat_map ~f:gather_first_message gs in
    if not (List.is_empty first_messages) then
      let encoded =
        List.fold ~init:encoded ~f:encode_progress_clause first_messages
      in
      match Expr.check_sat encoded with
      | `Unsat -> ()
      | _ -> uerr StuckRefinement
  in
  let rec aux env =
    ( if Pragma.validate_refinement_satisfiability () then
        let tyenv, _, _ = env in
        Expr.ensure_satisfiable tyenv ) ;
    function
    | EndG -> ()
    | MessageG (m, role_send, role_recv, g) ->
        let payloads = m.payload in
        let f (tenv, rvenv, role_knowledge) = function
          | PValue (v_opt, p_type) ->
              if Expr.is_well_formed_type tenv p_type then
                match v_opt with
                | Some v ->
                    let tenv = Expr.env_append tenv v p_type in
                    let role_knowledge =
                      knowledge_add role_knowledge role_recv v
                    in
                    let role_knowledge =
                      knowledge_add role_knowledge role_send v
                    in
                    let () =
                      match p_type with
                      | Expr.PTRefined (_, _, e) ->
                          if Pragma.sender_validate_refinements () then
                            ensure_knowledge role_knowledge role_send e ;
                          if Pragma.receiver_validate_refinements () then
                            ensure_knowledge role_knowledge role_recv e
                      | _ -> ()
                    in
                    (tenv, rvenv, role_knowledge)
                | None -> (tenv, rvenv, role_knowledge)
              else uerr (IllFormedPayloadType (Expr.show_payload_type p_type))
          | PDelegate _ -> unimpl ~here:[%here] "Delegation as payload"
        in
        let env = List.fold ~init:env ~f payloads in
        if Pragma.validate_refinement_progress () then ensure_progress env [g] ;
        aux env g
    | ChoiceG (_, gs) ->
        List.iter ~f:(aux env) gs ;
        if Pragma.validate_refinement_progress () then ensure_progress env gs
    | MuG (tvar, rec_vars, g) ->
        let f (tenv, rvenv, role_knowledge)
            {rv_name; rv_ty; rv_init_expr; rv_roles} =
          if Expr.is_well_formed_type tenv rv_ty then
            if Expr.check_type tenv rv_init_expr rv_ty then
              let tenv = Expr.env_append tenv rv_name rv_ty in
              let rvenv = Map.add_exn ~key:tvar ~data:rec_vars rvenv in
              let role_knowledge =
                List.fold ~init:role_knowledge
                  ~f:(fun acc role -> knowledge_add acc role rv_name)
                  rv_roles
              in
              (tenv, rvenv, role_knowledge)
            else
              uerr
                (TypeError
                   (Expr.show rv_init_expr, Expr.show_payload_type rv_ty) )
          else uerr (IllFormedPayloadType (Expr.show_payload_type rv_ty))
        in
        let env = List.fold ~init:env ~f rec_vars in
        aux env g
    | TVarG (tvar, rec_exprs, _) -> (
        let tenv, rvenv, role_knowledge = env in
        (* Unbound TypeVariable should not be possible, because it was
           previously validated *)
        let rec_vars = Option.value ~default:[] @@ Map.find rvenv tvar in
        match
          List.iter2
            ~f:(fun {rv_ty; rv_roles; _} rec_expr ->
              if Expr.check_type tenv rec_expr rv_ty then
                List.iter
                  ~f:(fun role ->
                    ensure_knowledge role_knowledge role rec_expr )
                  rv_roles
              else
                uerr
                  (TypeError
                     (Expr.show rec_expr, Expr.show_payload_type rv_ty) ) )
            rec_vars rec_exprs
        with
        | Base.List.Or_unequal_lengths.Ok () -> ()
        | Base.List.Or_unequal_lengths.Unequal_lengths ->
            unimpl ~here:[%here]
              "Error message for mismatched number of recursion variable \
               declaration and expressions" )
    | CallG _ -> assert false
  in
  aux env t

let add_missing_payload_field_names nested_t =
  let module Namegen = Namegen.Make (PayloadTypeName) in
  let add_missing_names namegen = function
    | PValue (None, n1) ->
        let payload_name_str =
          PayloadTypeName.of_string
            ("p_" ^ String.uncapitalize @@ Expr.show_payload_type n1)
        in
        let namegen, payload_name_str =
          Namegen.unique_name namegen payload_name_str
        in
        let payload_name =
          VariableName.of_other_name
            (module PayloadTypeName)
            payload_name_str
        in
        (namegen, PValue (Some payload_name, n1))
    | PValue (Some payload_name, n1) ->
        let payload_name_str =
          PayloadTypeName.create
            (String.uncapitalize @@ VariableName.user payload_name)
            (VariableName.where payload_name)
        in
        let namegen, payload_name_str =
          Namegen.unique_name namegen payload_name_str
        in
        let payload_name =
          VariableName.rename payload_name
            (PayloadTypeName.user payload_name_str)
        in
        (namegen, PValue (Some payload_name, n1))
    | PDelegate _ as p -> (namegen, p)
  in
  let rec add_missing_payload_names = function
    | MessageG (m, sender, recv, g) ->
        let g = add_missing_payload_names g in
        let {payload; _} = m in
        let namegen = Namegen.create () in
        let _, payload =
          List.fold_map payload ~init:namegen ~f:add_missing_names
        in
        MessageG ({m with payload}, sender, recv, g)
    | MuG (n, rec_vars, g) -> MuG (n, rec_vars, add_missing_payload_names g)
    | (TVarG _ | EndG) as p -> p
    | ChoiceG (r, gs) -> ChoiceG (r, List.map gs ~f:add_missing_payload_names)
    | CallG (caller, proto_name, roles, g) ->
        let g = add_missing_payload_names g in
        CallG (caller, proto_name, roles, g)
  in
  Map.map nested_t ~f:(fun ({gtype; _} as nested) ->
      {nested with gtype= add_missing_payload_names gtype} )

let nested_t_of_module (scr_module : Syntax.scr_module) =
  let open! Syntax in
  let scr_module = Extraction.rename_nested_protocols scr_module in
  let rec add_protocol protocols (protocol : global_protocol) =
    let nested_protocols = protocol.value.nested_protocols in
    let protocols =
      List.fold ~init:protocols ~f:add_protocol nested_protocols
    in
    let proto_name = protocol.value.name in
    let gtype = of_protocol protocol in
    let static_roles = protocol.value.split_roles.roles @ protocol.value.split_roles.reliable_roles in
    let dynamic_roles = protocol.value.split_roles.nested_roles in
    let nested_protocol_names =
      List.map ~f:(fun {Loc.value= {name; _}; _} -> name) nested_protocols
    in
    Map.add_exn protocols ~key:proto_name
      ~data:{static_roles; dynamic_roles; nested_protocol_names; gtype}
  in
  let all_protocols = scr_module.protocols @ scr_module.nested_protocols in
  let nested_t =
    List.fold
      ~init:(Map.empty (module ProtocolName))
      ~f:add_protocol all_protocols
  in
  normalise_nested_t @@ add_missing_payload_field_names nested_t


let add_to_set roles_to_ignore role set_of_roles = 
    if Set.mem roles_to_ignore role   
    then set_of_roles
    else Set.add set_of_roles role

let rec waiting_rs roles_to_ignore = function
    | MessageG (_, s, r, t) -> 
        waiting_rs roles_to_ignore t 
            |> add_to_set roles_to_ignore s 
            |> add_to_set roles_to_ignore r

    | ChoiceG (s, choices) ->
            let waiting_rs' = List.map ~f:(waiting_rs roles_to_ignore) choices in
            Set.union_list (module RoleName) waiting_rs' 
                |> add_to_set roles_to_ignore s

    | MuG (_, _, t) -> waiting_rs roles_to_ignore t

    | CallG (caller, _, roles, t) ->
            let rs_set = Set.of_list (module RoleName) roles in
            waiting_rs roles_to_ignore t 
                |> add_to_set roles_to_ignore caller 
                |> Set.union rs_set

    | _ -> Set.empty(module RoleName)

let flip f y x = f x y

let rec participants = function
    | MessageG (_, s, r, t) -> 
        participants t 
            |> flip Set.add s 
            |> flip Set.add r

    | ChoiceG (s, choices) ->
            let pts = List.map ~f:participants choices in
            Set.union_list (module RoleName) pts
                |> flip Set.add s

    | MuG (_, _, t) -> participants t

    | CallG (caller, _, roles, t) ->
            let rs_set = Set.of_list (module RoleName) roles in
            participants t 
                |> flip Set.add caller 
                |> Set.union rs_set

    | _ -> Set.empty(module RoleName)

let rec senders = function
    | MessageG (_, s, _, t) -> 
        senders t |> flip Set.add s 

    | ChoiceG (s, choices) ->
            let pts = List.map ~f:senders choices in
            Set.union_list (module RoleName) pts
                |> flip Set.add s

    | MuG (_, _, t) -> senders t

    | CallG (caller, _, _, t) -> senders t |> flip Set.add caller 

    | _ -> Set.empty(module RoleName)

let rec generate_crash_branch allow_local (t: t) crashed_r waiting_rs = 
    match t with
        | MessageG (msg, sender, receiver, t') ->
            let waiting_rs' = Set.remove waiting_rs receiver in
            let continuation = 
                generate_crash_branch allow_local t' crashed_r waiting_rs' in

            let sender_waiting = Set.mem waiting_rs sender in 
            let receiver_waiting = Set.mem waiting_rs receiver in
            let sender_crashed = RoleName.equal sender crashed_r in 
            let receiver_crashed = RoleName.equal receiver crashed_r in
            let label = if sender_crashed then "CRASH" else "EXIT" in

            let skip_communication = ((not sender_waiting) && (not receiver_waiting)) 
                                    || (receiver_crashed && not sender_waiting) in
            let notify = (sender_crashed || not sender_waiting) && receiver_waiting in

            if skip_communication 
                then continuation
            else if notify                 
                then MessageG ( {label = LabelName.of_string label; payload = []}
                              , sender
                              , receiver
                              , continuation)
            else if allow_local
                then MessageG ( msg
                              , sender
                              , receiver
                              , continuation)
            else
                uerr @@ UnawareOfCrash (sender, receiver)

        | ChoiceG (p, choices) ->
            (* with the assumption that every choice has a communication between sender and another role *)
            if RoleName.equal p crashed_r || not allow_local
            then 
                match List.hd choices with
                | Some (MessageG (m, s, r, t)) ->
                        let msg_g = MessageG (m, s, r, t) in
                        generate_crash_branch allow_local msg_g crashed_r waiting_rs 
                | _ -> unimpl ~here:[%here] 
                "Generating crash behaviour in choice that \ 
                does not start with a message" 
            else 
                ChoiceG ( p
                        , List.map choices
                            ~f: (fun ch -> generate_crash_branch allow_local ch crashed_r waiting_rs))

        | MuG (tvar, el, t) -> 
                MuG ( tvar
                    , el
                    , generate_crash_branch allow_local t crashed_r waiting_rs) 
        | CallG (caller, protocol, participants, t) -> 
                CallG ( caller
                      , protocol
                      , participants
                      , generate_crash_branch allow_local t crashed_r waiting_rs)
        | EndG -> EndG
        | other_t -> other_t

let apply_to_continuation f = function
    | MessageG (msg, s, r, t) -> MessageG(msg, s, r, f t)
    | g -> f g 
            

(* add crash branch whenever communication from an unreliable role is found *)
let rec add_crash_branches allow_local reliable_rs (gtype : t) = 
    match gtype with
        | MessageG (msg, sender, receiver, t) -> 
            if Set.mem reliable_rs sender 
            then 
                MessageG ( msg
                         , sender
                         , receiver
                         , add_crash_branches allow_local reliable_rs t)
            else
                let roles_to_ignore = 
                    Set.of_list (module RoleName) [sender; receiver] in
                let waiting_rs' = waiting_rs roles_to_ignore t in
                ChoiceG(
                sender,
                [ MessageG ({ label = LabelName.of_string "CRASH"; payload = [] } 
                            , sender 
                            , receiver 
                            , generate_crash_branch allow_local t sender waiting_rs')
                ; MessageG ( msg
                           , sender
                           , receiver
                           , add_crash_branches allow_local reliable_rs t)])

        | ChoiceG (sender, choices) ->
            let unfolded_choices = List.map ~f:unfold choices in
            (* with the assumption that we do not allow choice of choice of
             * we can assume that after unfolding all branches if they start
             * with a recursion, we are left 
             * only with messages as the first communication *)
            let some_branch = 
                match List.hd unfolded_choices with
                    | None -> EndG
                    | Some branch -> branch in
            let roles_to_ignore = Set.singleton (module RoleName) sender in
            let waiting_rs' = waiting_rs roles_to_ignore some_branch in
            let crash_branch =
                generate_crash_branch allow_local some_branch sender waiting_rs' in 
            let uncrashed_branches = 
                List.map
                ~f: (apply_to_continuation (add_crash_branches allow_local reliable_rs))
                unfolded_choices in
            if Set.mem reliable_rs sender
            then 
                ChoiceG(sender, uncrashed_branches)
            else
                ChoiceG(sender, crash_branch :: uncrashed_branches)

        | MuG (tvar, el, t) -> 
                MuG (tvar, el, add_crash_branches allow_local reliable_rs t)
        | CallG (c, p, pts, t) -> 
                CallG (c, p, pts, add_crash_branches allow_local reliable_rs t)
        | EndG -> EndG
        | other_t -> other_t


(* introduce crash patterns to global protocols *)
let graceful_failure (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let reliable_rs = global_protocol.value.split_roles.reliable_roles in
    let set_reliable_rs = Set.of_list (module RoleName) reliable_rs in
    let allow_local_comms = false in
    add_crash_branches allow_local_comms set_reliable_rs gtype 

let local_graceful_failure (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let reliable_rs = global_protocol.value.split_roles.reliable_roles in
    let set_reliable_rs = Set.of_list (module RoleName) reliable_rs in
    let allow_local_comms = true in
    add_crash_branches allow_local_comms set_reliable_rs gtype 



let update_role crashed_rs backups r =
    if Set.mem crashed_rs r
    then 
        match Map.find backups r with
        | Some b -> b
        | None -> r (*this branch will be taken by crashed roles
                      that do not have a backup*)
    else
        r

let rec replace crashed_rs backups = function
    | MessageG (m, p, q, t) ->
            let p' = update_role crashed_rs backups p in
            let q' = update_role crashed_rs backups q in
            MessageG (m, p', q', replace crashed_rs backups t)

    | ChoiceG (p, choices) ->
            let p' = update_role crashed_rs backups p in
            ChoiceG (p', List.map ~f:(replace crashed_rs backups) choices )

    
    | MuG (_, _, t) -> replace crashed_rs backups t
    | CallG (caller, protocol, participants, t) -> 
            let caller = update_role crashed_rs backups caller in
            CallG ( caller 
                  , protocol
                  , participants
                  , replace crashed_rs backups t)
    | EndG -> EndG
    | other_t -> other_t

let rec notify q waiting_rs label init = 
    Set.fold
        ~f: (fun accum r -> 
        let m = 
            { label = LabelName.of_string label ; payload = [] } in 
            MessageG (m, q, r, accum))
        ~init: init 
        waiting_rs 


(*TODO: Think how to group parameters, function calls are too long*)
(*Or maybe just have labeled arguments to make it clear and also format code nicer*)
let rec add_failover_branches 
    ~rel_rs: rel_rs 
    ~crashed_rs: crashed_rs 
    ~handled_rs: handled_rs
    ~backups: backups 
    ~notif: notif
    ~notifiers: notifiers (* mapping from an unreliable role with
                            a backup to its corresponding notifier
                            i.e either last role that received 
                            a message from it, or notif *)
    ~aware_of_rs: aware_of_rs (* mapping from role to crashed roles that it is 
                                aware of *)
    ~glb_prot: glb_prot (* global protocol that needs to be restarted 
                           from beginning but with backups replacing 
                           crashed roles *)
    = function
    | MessageG (m, p, q, t) -> 
        let p_crashed = Map.mem crashed_rs p in
        let q_crashed = Map.mem notifiers q in
        let p_reliable = Set.mem rel_rs p in
        let q_reliable = Set.mem rel_rs q in
        let p_handled = Set.mem handled_rs p in

        let p_unrel_no_bckup = not p_reliable && not (Map.mem backups p) in

        if q_crashed && ( match Map.find aware_of_rs p with
                            | None -> false
                            | Some rs -> Set.mem rs q )
        then
            add_failover_branches 
                    ~rel_rs: rel_rs
                    ~crashed_rs: crashed_rs
                    ~handled_rs: handled_rs
                    ~backups: backups
                    ~notif: notif
                    ~notifiers: notifiers
                    ~aware_of_rs: aware_of_rs
                    ~glb_prot: glb_prot
                    t

        else if p_unrel_no_bckup && not p_handled
        then
            (*use local graceful failure if there is no backup*)
            let crash_branch = 
                let handled_rs' = Set.add handled_rs p in
                let cont = 
                    add_failover_branches 
                            ~rel_rs: rel_rs
                            ~crashed_rs: crashed_rs
                            ~handled_rs: handled_rs'
                            ~backups: backups
                            ~notif: notif
                            ~notifiers: notifiers 
                            ~aware_of_rs: aware_of_rs
                            ~glb_prot: glb_prot
                            t in
                let notified_rs = Set.of_list (module RoleName) [p ; q] in
                let waiting_rs = 
                    participants cont |> flip Set.diff notified_rs in 
                let allow_local = true in
                let crash_m = { label = 
                                   LabelName.of_string "CRASH"
                               ; payload =
                                   [] } in
                MessageG ( crash_m
                         , p
                         , q
                         , generate_crash_branch allow_local cont p waiting_rs )
            in
            let noncrash_branch = 
                MessageG ( m
                         , p
                         , q
                         , add_failover_branches 
                                ~rel_rs: rel_rs
                                ~crashed_rs: crashed_rs
                                ~handled_rs: handled_rs
                                ~backups: backups
                                ~notif: notif
                                ~notifiers: notifiers
                                ~aware_of_rs: aware_of_rs
                                ~glb_prot: glb_prot
                                t )
            in 
            ChoiceG (p, [crash_branch; noncrash_branch])

        else if p_handled
        then
                MessageG (m, p, q, 
                    add_failover_branches 
                        ~rel_rs: rel_rs
                        ~crashed_rs: crashed_rs
                        ~handled_rs: handled_rs
                        ~backups: backups
                        ~notif: notif
                        ~notifiers: notifiers
                        ~aware_of_rs: aware_of_rs
                        ~glb_prot: glb_prot
                        t)

        else if p_reliable
        then
        (*
            let p_aware_of = 
                match Map.find aware_of_rs p with
                | Some rs -> rs
                | None -> Set.empty (module RoleName) in
            let q_aware_of =
                match Map.find aware_of_rs q with
                | Some rs -> rs
                | None -> Set.empty (module RoleName) in
            let notify_about_rs = Set.diff p_aware_of q_aware_of in
            let aware_of_rs' = 
                Map.update aware_of_rs q
                    ~f: (fun v -> match v with
                                | Some rs -> Set.union rs notify_about_rs
                                | None -> notify_about_rs) in
            let cont = MessageG (m, p, q, 
                            add_failover_branches 
                                ~rel_rs: rel_rs
                                ~crashed_rs: crashed_rs
                                ~handled_rs: handled_rs
                                ~backups: backups
                                ~notif: notif
                                ~notifiers: notifiers
                                ~aware_of_rs: aware_of_rs'
                                ~glb_prot: glb_prot
                                t)
            in
            if Set.is_empty notify_about_rs 
            then *)
                MessageG (m, p, q, 
                            add_failover_branches 
                                ~rel_rs: rel_rs
                                ~crashed_rs: crashed_rs
                                ~handled_rs: handled_rs
                                ~backups: backups
                                ~notif: notif
                                ~notifiers: notifiers
                                ~aware_of_rs: aware_of_rs
                                ~glb_prot: glb_prot
                                t)

            (* else
                let label = 
                    Set.fold
                        ~f: (fun accum r -> accum ^ RoleName.user r)
                        ~init: "CRASHED-"
                        notify_about_rs in
                let crash_m = { label = 
                                   LabelName.of_string label
                               ; payload =
                                   [] } in
                MessageG (crash_m, p, q, cont) *)
        else

        let senders = senders t in
        let b = 
            match Map.find backups p with
            | Some b' -> b'
            | None -> p (* this branch will never be taken*)
        in

        if not (Set.mem senders p)
        then
            if p_crashed
            (*notifier is required to send message to backup 
        and notify all unaware roles*)
            then
                let aware_of_p = 
                    match Map.find aware_of_rs q with
                    | Some rs -> Set.mem rs p
                    | None -> false in 
                let aware_of_rs' = 
                    Map.update aware_of_rs q 
                        ~f: (fun v -> match v with
                                | Some rs -> Set.add rs p
                                | None -> Set.singleton (module RoleName) p) 
                in
                let crash_m = { label = 
                                   LabelName.of_string "CRASH"
                               ; payload =
                                   [] } 
                in 
                let cont = add_failover_branches 
                                    ~rel_rs: rel_rs
                                    ~crashed_rs: crashed_rs
                                    ~handled_rs: handled_rs
                                    ~backups: backups
                                    ~notif: notif
                                    ~notifiers: notifiers
                                    ~aware_of_rs: aware_of_rs'
                                    ~glb_prot: glb_prot 
                                    t in
                match Map.find notifiers p with
                | None -> 
                (*that means declared notifier must be used*)
                ( match notif with
                        | Some n ->
                            (* if aware_of_p
                            then use_notifier
                            else MessageG(crash_m, p, q, use_notifier) *)
                            let aware_of_p = 
                                match Map.find aware_of_rs n with
                                | Some rs -> Set.mem rs p
                                | None -> false in
                            if aware_of_p
                            then cont
                            else MessageG(crash_m, p, n, cont)
                    | None ->
                        uerr @@ ReliabilityInformationLoss (p, q) )
                | Some r -> 
                if q_reliable
                then
                    (* let crashed_rs_notif' = 
                        Map.update notifiers p 
                        ~f: (fun v -> match v with | _ -> q ) in *)
                    let cont = add_failover_branches 
                                    ~rel_rs: rel_rs
                                    ~crashed_rs: crashed_rs
                                    ~handled_rs: handled_rs
                                    ~backups: backups
                                    ~notif: notif
                                    ~notifiers: notifiers 
                                    ~aware_of_rs: aware_of_rs'
                                    ~glb_prot: glb_prot
                                    t in
                    (* let notified_rs = 
                        Map.fold aware_of_rs' 
                            ~init: (Set.empty (module RoleName))
                            ~f: (fun ~key:k ~data:rs acc -> 
                                if Set.mem rs p then Set.add acc k else acc) 
                    in 
                    let not_aware_rs = 
                        participants glb_prot
                        |> flip Set.diff notified_rs
                        |> flip Set.diff crashed_rs in
                    let label = "CRASHED-" ^ RoleName.user p in
                    (*q can be used as notifier*) 
                    let notify_rs = notify q not_aware_rs label cont in 
                    let backup_m = { label = 
                                       LabelName.of_string "START"
                                   ; payload =
                                       [] } in *)
                    
                    if aware_of_p
                    then
                       (* MessageG (backup_m, q, b, notify_rs) *)
                        cont
                    else 
                        (* MessageG (crash_m, p, q,
                            MessageG(backup_m, q , b , notify_rs)) *)
                        MessageG (crash_m, p, q, cont)
                else
                    match notif with 
                    | Some n ->
                        let crashed_rs_notif' = 
                            Map.update crashed_rs_notif p 
                            ~f: (fun v -> match v with | _ -> n ) in
                        (* let use_notifier = *)
                        let cont = 
                            (* MessageG (crash_m, p, n, t) |> *)
                                add_failover_branches 
                                    ~rel_rs: rel_rs
                                    ~crashed_rs: crashed_rs
                                    ~handled_rs: handled_rs
                                    ~backups: backups
                                    ~notif: notif
                                    ~crashed_rs_notif: crashed_rs_notif'
                                    ~aware_of_rs: aware_of_rs'
                                    ~glb_prot: glb_prot 
                                    t in
                        (* if aware_of_p
                        then use_notifier
                        else MessageG(crash_m, p, q, use_notifier) *)
                        if aware_of_p
                        then cont
                        else MessageG(crash_m, p, q, cont)

                    | None ->
                        uerr @@ ReliabilityInformationLoss (p, q)

            else 
                let crash_branch = 
                    let crashed_rs' = Set.add crashed_rs p in
                    MessageG( { label = 
                                    LabelName.of_string "CRASH"
                              ; payload =
                                    [] }
                            , p
                            , q
                            , t) 
                    |> add_failover_branches 
                        ~rel_rs: rel_rs
                        ~crashed_rs: crashed_rs'
                        ~handled_rs: handled_rs
                        ~backups: backups
                        ~notif: notif
                        ~aware_of_rs: aware_of_rs
                        ~glb_prot: glb_prot  in

                let noncrash_branch = 
                    if q_reliable
                    then
                    (*TODO: remove p as key from waiting_rs *)
                    let cont = add_failover_branches 
                                    ~rel_rs: rel_rs
                                    ~crashed_rs: crashed_rs
                                    ~handled_rs: handled_rs
                                    ~backups: backups
                                    ~notif: notif
                                    ~crashed_rs_notif: crashed_rs_notif
                                    ~aware_of_rs: aware_of_rs
                                    ~glb_prot: glb_prot
                                    t in
                    let notified_rs = Set.of_list (module RoleName) [p ; q] in
                    let not_aware_rs = 
                        participants glb_prot
                        |> flip Set.diff notified_rs
                        |> flip Set.diff crashed_rs in
                    let label = "SAFE-" ^ RoleName.user p in
                    let backup_m = { label = 
                                       LabelName.of_string "SAFE"
                                   ; payload =
                                       [] } in
                    (*q can be used as notifier*) 
                    let notify_rs = notify q not_aware_rs label cont in
                    MessageG (m, p, q,
                        MessageG(backup_m, q, b, notify_rs))
                    else
                        match notif with
                        | Some n ->
                            let notif_m = { label = 
                                               LabelName.of_string "DUMMY"
                                           ; payload =
                                               [] } in
                            let use_notifier = 
                                MessageG (notif_m, p, n, t)
                                    |> add_failover_branches 
                                        ~rel_rs: rel_rs
                                        ~crashed_rs: crashed_rs
                                        ~handled_rs: handled_rs
                                        ~backups: backups
                                        ~notif: notif
                                        ~aware_of_rs: aware_of_rs
                                        ~glb_prot: glb_prot in
                            MessageG(m, p, q, use_notifier)
                        | None ->
                            uerr @@ ReliabilityInformationLoss (p, q)
                    in
                    ChoiceG (p, [noncrash_branch ; crash_branch])
            else
                if p_crashed
                then
                    let aware_of_rs' = 
                        Map.update aware_of_rs q 
                            ~f: (fun v -> match v with
                                | Some rs -> Set.add rs p
                                | None -> Set.singleton (module RoleName) p) 
                    in
                    MessageG ( { label = 
                                   LabelName.of_string "CRASH"
                               ; payload =
                                   [] } 
                             , p
                             , q
                             , add_failover_branches 
                                        ~rel_rs: rel_rs
                                        ~crashed_rs: crashed_rs
                                        ~handled_rs: handled_rs
                                        ~backups: backups
                                        ~notif: notif
                                        ~aware_of_rs: aware_of_rs'
                                        ~glb_prot: glb_prot 
                                        t ) 
                else 
                    let crash_branch = 
                        let crashed_rs' = Set.add crashed_rs p in
                        let aware_of_rs' = 
                            Map.update aware_of_rs q 
                                ~f: (fun v -> match v with
                                    | Some rs -> Set.add rs p
                                    | None -> Set.singleton (module RoleName) p) 
                        in
                        MessageG ( { label = 
                                       LabelName.of_string "CRASH"
                                   ; payload =
                                       [] } 
                                 , p
                                 , q
                                 , add_failover_branches 
                                            ~rel_rs: rel_rs
                                            ~crashed_rs: crashed_rs'
                                            ~handled_rs: handled_rs
                                            ~backups: backups
                                            ~notif: notif
                                            ~aware_of_rs: aware_of_rs'
                                            ~glb_prot: glb_prot 
                                            t ) in
                    let noncrash_branch = 
                        MessageG ( m, p, q
                                 , add_failover_branches 
                                            ~rel_rs: rel_rs
                                            ~crashed_rs: crashed_rs
                                            ~handled_rs: handled_rs
                                            ~backups: backups
                                            ~notif: notif
                                            ~aware_of_rs: aware_of_rs
                                            ~glb_prot: glb_prot 
                                            t ) in
                    ChoiceG (p, [crash_branch ; noncrash_branch])

    | ChoiceG (p, choices) ->
            let extended_choices = 
                List.map
                (*might need to use apply_to_continuation*)
                ~f: (fun ch -> apply_to_continuation 
                                    (add_failover_branches 
                                        ~rel_rs: rel_rs
                                        ~crashed_rs: crashed_rs
                                        ~handled_rs: handled_rs
                                        ~backups: backups
                                        ~aware_of_rs: aware_of_rs
                                        ~notif: notif
                                        ~glb_prot: glb_prot)
                                ch )
                choices in
            if Set.mem (Set.union rel_rs handled_rs) p 
            then 
                ChoiceG (p, extended_choices)
            else
            let some_branch = 
                match List.hd choices with
                    | None -> EndG
                    | Some branch -> branch in
            let q = 
                match some_branch with
                    | MessageG (_, _, q, _) -> q
                    | _ -> p
            in
            let b = 
                match Map.find backups p with
                | None -> p (*this branch will never be taken*)
                | Some b' -> b' in
            let rel_rs' = Set.add rel_rs b in
            let crashed_rs' = Set.add crashed_rs p in
            let aware_of_rs' = 
                Map.update aware_of_rs q 
                    ~f: (fun v -> match v with
                            | Some rs -> Set.add rs p
                            | None -> Set.singleton (module RoleName) p) 
            in
            let crash_branch = add_failover_branches 
                                        ~rel_rs: rel_rs'
                                        ~crashed_rs: crashed_rs'
                                        ~handled_rs: handled_rs
                                        ~backups: backups
                                        ~aware_of_rs: aware_of_rs'
                                        ~notif: notif
                                        ~glb_prot: glb_prot
                                        some_branch in
            ChoiceG (p, crash_branch :: extended_choices) 

    | EndG ->
        if Set.is_empty crashed_rs
        then EndG
        else 
            let glb_prot' = replace crashed_rs backups glb_prot in
            let handled_rs' = Set.union handled_rs crashed_rs in
            let crashed_rs' = Set.empty (module RoleName) in
            let aware_of_rs' = Map.empty (module RoleName) in
                    add_failover_branches 
                        ~rel_rs: rel_rs
                        ~crashed_rs: crashed_rs'
                        ~handled_rs: handled_rs'
                        ~backups: backups
                        ~aware_of_rs: aware_of_rs'
                        ~notif: notif
                        ~glb_prot: glb_prot'
                        glb_prot'

    | MuG (tvar, el, t) -> 
            MuG ( tvar
                , el
                , add_failover_branches 
                            ~rel_rs: rel_rs
                            ~crashed_rs: crashed_rs
                            ~handled_rs: handled_rs
                            ~backups: backups
                            ~aware_of_rs: aware_of_rs
                            ~notif: notif
                            ~glb_prot: glb_prot
                            t ) 

    | CallG (c, p, pts, t) -> 
            CallG ( c
                  , p
                  , pts
                  , add_failover_branches 
                            ~rel_rs: rel_rs
                            ~crashed_rs: crashed_rs
                            ~handled_rs: handled_rs
                            ~backups: backups
                            ~aware_of_rs: aware_of_rs
                            ~notif: notif
                            ~glb_prot: glb_prot
                            t ) 
    | _ -> EndG


let failover (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let rel_rs = global_protocol.value.split_roles.reliable_roles in
    let rel_rs = Set.of_list (module RoleName) rel_rs in
    let notifier = global_protocol.value.split_roles.notifier in
    let backups = global_protocol.value.split_roles.backups_map in
    let backups = 
        match Map.of_alist (module RoleName) backups with
        | `Ok bckps -> bckps
        (*TODO: raise error for duplicate*)
        | `Duplicate_key _  -> Map.empty(module RoleName) in
    let crashed_rs = Set.empty (module RoleName) in
    let aware_of_rs = Map.empty (module RoleName) in
    let handled_rs = Set.empty (module RoleName) in
    (*add failover behaviour for roles with backups*)
    add_failover_branches 
            ~rel_rs: rel_rs
            ~crashed_rs: crashed_rs
            ~handled_rs: handled_rs
            ~backups: backups
            ~aware_of_rs: aware_of_rs
            ~notif: notifier
            ~glb_prot: gtype
            gtype
