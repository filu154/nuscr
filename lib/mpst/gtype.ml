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
    | EndG -> pp_print_string ppf "" (*TODO: This was (end) before*)
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

(* Module used for basic graceful failure 
module RoleNamePair = struct
    module Pair = struct
        type t = RoleName.t * RoleName.t [@@deriving ord, sexp_of]
    end
    include Pair
    include Comparator.Make (Pair)
end
*)

let rec _basic_generate_crash_branch crashed_r = function 
    | MessageG (_, sender, receiver, t') ->
        let label = if RoleName.equal crashed_r sender then "CRASH" else "EXIT" in
            MessageG ( {label = LabelName.of_string label; payload = []} 
                      , sender
                      , receiver
                      , _basic_generate_crash_branch crashed_r t' )

        | ChoiceG (_, choices) ->
            (* with the assumption that every choice has a communication between sender and another role *)
                ( match List.hd choices with
                | Some ch->
                        _basic_generate_crash_branch crashed_r ch 
                | _ -> unimpl ~here:[%here] 
                "Generating crash behaviour in choice that" )

        | MuG (tvar, el, t) -> 
                MuG ( tvar
                    , el
                    , _basic_generate_crash_branch crashed_r t) 
        | CallG (caller, protocol, participants, t) -> 
                CallG ( caller
                      , protocol
                      , participants
                      , _basic_generate_crash_branch crashed_r t)
        | EndG -> EndG
        | other_t -> other_t
            

let rec _basic_crash_branch_lgf aware crashed_r = function 
    | MessageG (m, sender, receiver, t') ->
        let label = if RoleName.equal crashed_r sender then "CRASH" else "EXIT" in
        if Set.mem aware sender 
        then
            let aware' = Set.add aware receiver in
            MessageG ( {label = LabelName.of_string label; payload = []} 
                      , sender
                      , receiver
                      , _basic_crash_branch_lgf aware' crashed_r t' )
        else MessageG (m, sender, receiver , _basic_crash_branch_lgf aware crashed_r t')

        | ChoiceG (_, choices) ->
            (* with the assumption that every choice has a communication between sender and another role *)
                ( match List.hd choices with
                | Some ch->
                        _basic_generate_crash_branch crashed_r ch 
                | _ -> unimpl ~here:[%here] 
                "Generating crash behaviour in choice that" )

        | MuG (tvar, el, t) -> 
                MuG ( tvar
                    , el
                    , _basic_generate_crash_branch crashed_r t) 
        | CallG (caller, protocol, participants, t) -> 
                CallG ( caller
                      , protocol
                      , participants
                      , _basic_generate_crash_branch crashed_r t)
        | EndG -> EndG
        | other_t -> other_t

let update_indices indices r = 
    let index = Map.find_exn indices r in
    Map.set indices ~key:r ~data:(index + 1)

let indexed_role indices r = 
    let index = Map.find_exn indices r in
    RoleName.of_string (RoleName.user r ^ "-" ^ Int.to_string index)

let gf_skip csp p q =
    let p_csp = Map.find csp p 
            |> Option.value ~default:(Set.empty (module RoleName)) in
    let q_csp = Map.find csp q 
            |> Option.value ~default:(Set.empty (module RoleName)) in
    let non_empty = not (Set.is_empty p_csp) && not (Set.is_empty q_csp) in
    non_empty && not (Set.is_empty (Set.inter p_csp q_csp))

let update_gf_param rel_rs indices lcp csp p q = 
    let p_rel = Set.mem rel_rs p in
    let indices' = if not p_rel then update_indices indices p else indices in
    let lcp' = 
        if p_rel then Map.update lcp q ~f:(function | _ -> Map.find_exn lcp p)
        else 
        let lcp_inter = Map.update lcp q ~f:(function | _ -> indexed_role indices p) 
        in Map.update lcp_inter p ~f:(function | _ -> indexed_role indices p)
    in
    let csp' = 
        if p_rel then Map.update csp q ~f:(function 
            | None -> Map.find_exn lcp p |> Set.singleton (module RoleName) 
            | Some s -> Map.find_exn lcp p |> Set.add s)
        else 
            let csp_inter = Map.update csp q ~f:(function 
                | None -> indexed_role indices p |> Set.singleton (module RoleName) 
                | Some s -> Set.add s (indexed_role indices p))
            in Map.update csp_inter p ~f:(function 
                | None -> indexed_role indices p |> Set.singleton (module RoleName) 
                | Some s -> Set.add s (indexed_role indices p))
    in (indices', lcp', csp')


let rec _crash_branch ~rel_rs ~indices ~crs ~lcp ~csp ~rec_t ~unf = function
        | MessageG (_, p, q, t') ->
            let p_crashed = Set.mem crs p in
            let q_crashed = Set.mem crs q in
            let p_rel = Set.mem rel_rs p in
            let gf_skip_cond = gf_skip csp p q in
            let (indices', lcp', csp') = update_gf_param rel_rs indices lcp csp p q in

            if p_crashed && q_crashed
            then _crash_branch ~rel_rs ~indices:indices' 
                               ~crs ~lcp:lcp' ~csp:csp' ~rec_t ~unf t'
            else if gf_skip_cond
            then _crash_branch ~rel_rs ~indices:indices' 
                               ~crs ~lcp:lcp' ~csp:csp' ~rec_t ~unf t'
            else if p_crashed && (not gf_skip_cond)
            then
                MessageG ( {label = LabelName.of_string "CRASH"; payload = []}
                          , p , q
                          , _crash_branch ~rel_rs ~indices:indices' 
                          ~crs ~lcp:lcp' ~csp:csp' ~rec_t ~unf t')
            (*check that sender is aware of crash*)
            else if not (Map.mem csp p) 
            then uerr @@ UnawareOfCrash (p, q)
            else if p_rel && (not gf_skip_cond)
            then
                MessageG ( {label = LabelName.of_string "EXIT"; payload = []}
                          , p , q
                          , _crash_branch ~rel_rs ~indices:indices' 
                          ~crs ~lcp:lcp' ~csp:csp' ~rec_t ~unf t')
            else 
            let crs' = Set.add crs p in
            ChoiceG ( p
                    , [ MessageG ( {label = LabelName.of_string "CRASH"; payload = []}
                                , p , q
                                , _crash_branch ~rel_rs ~indices:indices' 
                                ~crs:crs' ~lcp:lcp' ~csp:csp' ~rec_t ~unf t')
                    ; MessageG ( {label = LabelName.of_string "EXIT"; payload = []}
                                , p , q
                                , _crash_branch ~rel_rs ~indices:indices' 
                                ~crs ~lcp:lcp' ~csp:csp' ~rec_t ~unf t')])

        | ChoiceG (_, choices) ->
            ( match List.hd choices with
            | Some some_branch ->
                    _crash_branch ~rel_rs ~indices 
                                  ~crs ~lcp ~csp ~rec_t ~unf some_branch
            | _ -> unimpl ~here:[%here] 
            "Generating crash behaviour in empty choice" ) 

        | MuG (tvar, _, t) -> 
                let rec_t' = Map.add_exn rec_t ~key:tvar ~data:t in
                let cont = _crash_branch ~rel_rs ~indices ~crs ~lcp ~csp 
                                         ~rec_t:rec_t' ~unf t in
                cont
        | TVarG (tvar, _, _) -> 
                let t' = if Set.mem unf tvar 
                         then EndG
                         else Map.find_exn rec_t tvar in
                let unf' = Set.add unf tvar in
                _crash_branch ~rel_rs ~indices ~crs ~lcp ~csp 
                                         ~rec_t ~unf:unf' t' 
        | CallG (caller, protocol, participants, t) -> 
                CallG ( caller
                      , protocol
                      , participants
                      , _crash_branch ~rel_rs ~indices ~crs ~lcp ~csp ~unf ~rec_t t)
        | EndG -> EndG

let aware_of_crash crs pcp p = Map.mem pcp p || Set.mem crs p

let update_lgf_aw rel_rs indices aw p q = 
    if Set.mem rel_rs p 
    then Map.map aw ~f:(fun s -> if Set.mem s p then Set.add s q else s)
    else 
        let p_indexed = indexed_role indices p in
        let new_entry = Set.of_list (module RoleName) [p ; q] in
        Map.add_exn aw ~key:p_indexed ~data:new_entry

let update_lgf_cb crs cb pcp p q = 
    if aware_of_crash crs pcp p 
    then Set.add cb (p,q) |> flip Set.add (q,p)
    else cb

let update_lgf_pcp indices crs pcp aw p q = 
    if aware_of_crash crs pcp p
    then if aware_of_crash crs pcp q 
        then pcp (*skip update if q is aware of crash*)
        else if Set.mem crs p
            (*q unaware, p crashed, set only to p indexed*)
            then Map.add_exn pcp ~key:q 
                ~data: (indexed_role indices p 
                        |> Set.singleton (module RoleName))
           (*q unaware, p not crashed, set to all possible crash points*)
           else let new_entry = Map.fold aw 
                                ~init: (Set.empty (module RoleName))
                                ~f:(fun ~key ~data acc -> 
                                    if Set.mem data p 
                                    then Set.add acc key 
                                    else acc)
            in Map.add_exn pcp ~key:q ~data:new_entry 
    else pcp

let _update_lgf_param rel_rs indices crs cb pcp aw p q = 
    let p_rel = Set.mem rel_rs p in
    let indices' = if not p_rel then update_indices indices p else indices in
    let aw' = update_lgf_aw rel_rs indices aw p q in
    let cb' = update_lgf_cb crs cb pcp p q in
    let pcp' = update_lgf_pcp indices crs pcp aw p q in
    (indices', cb', pcp', aw')

let lgf_skip cb pcp aw p q =
    let comm_already = Set.mem cb (p,q) in
    let aware_p = Map.mem pcp p in
    let aware_q = Map.mem pcp q in
    let cond_p = if aware_p 
                 then let pcp_p = Map.find_exn pcp p in
                 Set.fold pcp_p ~init:true 
                 ~f:(fun acc r -> 
                     let aw_r = Map.find_exn aw r in
                     acc && Set.mem aw_r q)
                 else true in
    let cond_q = if aware_q 
                 then let pcp_q = Map.find_exn pcp q in
                 Set.fold pcp_q ~init:true 
                 ~f:(fun acc r -> 
                     let aw_r = Map.find_exn aw r in
                     acc && Set.mem aw_r p)
                 else true in
    comm_already || ((aware_p || aware_q) && cond_p && cond_q)

let apply_to_continuation f = function
    | MessageG (msg, s, r, t) -> MessageG(msg, s, r, f t)
    | g -> f g 

let rec _crash_branch_lgf 
    ~rel_rs ~indices ~crs ~cb ~pcp ~aw ~a ~rec_t = function
    | MessageG(m, p, q, t) ->
        let p_rel = Set.mem rel_rs p in
        let indices' = if not p_rel then update_indices indices p else indices in
        let aw' = update_lgf_aw rel_rs indices aw p q in

        let p_crashed = Set.mem crs p in
        let q_crashed = Set.mem crs q in

        if p_rel && not (aware_of_crash crs pcp p) 
        (*p is reliable but not aware of crash*)
        then MessageG( m, p, q
                     , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                         ~crs ~cb ~pcp ~aw:aw' ~a ~rec_t t)
        else if not p_rel && not (aware_of_crash crs pcp p)
        then 
        (*p is unreliable but not aware of crash*)
            let safe_branch = 
                MessageG( m, p, q
                        , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                            ~crs ~cb ~pcp 
                                            ~aw:aw' ~a ~rec_t t) in
            let crash_branch = 
                let crs' = Set.add crs p in
                let cb' = update_lgf_cb crs' cb pcp p q in
                let pcp' = update_lgf_pcp indices crs' pcp aw p q in
                let a' = Set.add a p |> flip Set.add q in
                MessageG( {label = LabelName.of_string "CRASH"; payload = []}
                        , p, q
                        , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                            ~crs:crs' ~cb:cb' ~pcp:pcp' 
                                            ~aw:aw' ~a:a' ~rec_t t) 
            in
            ChoiceG( p, [safe_branch; crash_branch])
        else if p_crashed && q_crashed
        then _crash_branch_lgf ~rel_rs ~indices:indices' 
                               ~crs ~cb ~pcp ~aw:aw' ~a ~rec_t t
        else if p_crashed 
        then if not (lgf_skip cb pcp aw p q)
             then
             let cb' = update_lgf_cb crs cb pcp p q in
             let pcp' = update_lgf_pcp indices crs pcp aw p q in
             let a' = Set.add a q in
             MessageG( {label = LabelName.of_string "CRASH"; payload = []}
                     , p, q
                     , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                        ~crs ~cb:cb' ~pcp:pcp' 
                                        ~aw:aw' ~a:a' ~rec_t t)
             else _crash_branch_lgf ~rel_rs ~indices:indices' 
                                  ~crs ~cb ~pcp ~aw:aw' ~a ~rec_t t
        else if lgf_skip cb pcp aw p q
        then _crash_branch_lgf ~rel_rs ~indices:indices' 
                               ~crs ~cb ~pcp ~aw:aw' ~a ~rec_t t
        else 
            (*they communicate about a crash*)
            let cb' = update_lgf_cb crs cb pcp p q in
            let a' = Set.add a q in
            if p_rel
            then
                let pcp' = update_lgf_pcp indices crs pcp aw p q in
                MessageG( {label = LabelName.of_string "EXIT"; payload = []}
                        , p, q
                        , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                            ~crs ~cb:cb' ~pcp:pcp'
                                            ~aw:aw' ~a:a' ~rec_t t)
            else
            let safe_branch =
                (*q infers p's possible crash points*)
                let pcp' = update_lgf_pcp indices crs pcp aw p q in
             MessageG( {label = LabelName.of_string "EXIT"; payload = []}
                     , p, q
                     , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                        ~crs ~cb:cb' ~pcp:pcp' 
                                        ~aw:aw' ~a:a' ~rec_t t) in
            let crash_branch =
                let crs' = Set.add crs p in
                let cb' = update_lgf_cb crs' cb pcp p q in
                let pcp' = update_lgf_pcp indices crs' pcp aw p q in
                MessageG( {label = LabelName.of_string "CRASH"; payload = []}
                        , p, q
                        , _crash_branch_lgf ~rel_rs ~indices:indices' 
                                            ~crs:crs' ~cb:cb' ~pcp:pcp' 
                                            ~aw:aw' ~a:a' ~rec_t t) in
            ChoiceG( p, [safe_branch; crash_branch])

    | ChoiceG (p, choices) ->
        let some_branch = 
            match List.hd choices with
                | None -> EndG
                | Some branch -> branch in
        let q = match some_branch with
            | MessageG (_, _, q, _) -> q
            | _ -> unimpl ~here:[%here] "Choice with non-message branch" in
        let aw' = update_lgf_aw rel_rs indices aw p q in
        let indices' = if not (Set.mem rel_rs p)
                       then update_indices indices p 
                       else indices in
        if Set.mem rel_rs p && not (aware_of_crash crs pcp p)
        then
            ChoiceG(p, List.map choices
                    ~f: (apply_to_continuation 
                        (_crash_branch_lgf ~rel_rs ~indices ~crs ~cb ~pcp 
                                           ~aw:aw' ~a ~rec_t))) 
        else if not (Set.mem rel_rs p) && not (aware_of_crash crs pcp p)
        then 
            (*p is not crashed but it is unreliable*)
            let a' = Set.add a p |> flip Set.add q in
            let crash_branch = 
                let crs' = Set.add crs p in
                _crash_branch_lgf ~rel_rs ~indices:indices' ~crs:crs' ~cb
                                  ~pcp ~aw:aw' ~a:a' ~rec_t some_branch in
            ChoiceG(p, crash_branch :: List.map choices
                ~f: (apply_to_continuation 
                    (_crash_branch_lgf ~rel_rs ~indices:indices' ~crs ~cb 
                                       ~pcp ~aw:aw' ~a ~rec_t)))
        else
            let a' = Set.add a q in
            _crash_branch_lgf ~rel_rs ~indices:indices' ~crs ~cb ~pcp 
                              ~aw: aw' ~a:a' ~rec_t some_branch

    | MuG (tvar, el, t) -> 
            let rec_t' = Map.add_exn rec_t ~key:tvar ~data:t in
            if not (Set.is_empty crs)
            then _crash_branch_lgf ~rel_rs ~indices ~crs ~cb ~pcp 
                                   ~aw ~a ~rec_t:rec_t' t
            else
            MuG (tvar, el, _crash_branch_lgf ~rel_rs ~indices ~crs ~cb ~pcp ~aw
                                         ~a ~rec_t:rec_t' t)
    | TVarG (tvar, es, t) -> 
            if Set.is_empty a 
            then if Set.is_empty crs
                 then TVarG(tvar, es, t) (*no crash happened*)
                 else EndG (*unfolding does not result in new comms*)
            else 
            let a' = Set.empty (module RoleName) in
            Map.find_exn rec_t tvar 
            |> _crash_branch_lgf ~rel_rs ~indices ~crs ~cb ~pcp ~aw ~a:a' ~rec_t 

    | CallG (caller, protocol, participants, t) -> 
            CallG ( caller
                  , protocol
                  , participants
                  , _crash_branch_lgf ~rel_rs ~indices ~crs ~cb 
                                      ~pcp ~aw ~a ~rec_t t)
    | EndG -> EndG

                



let rec _basic_add_crash_branches reliable_rs = function
    | MessageG (msg, sender, receiver, t) -> 
        if Set.mem reliable_rs sender 
        then 
            MessageG ( msg
                     , sender
                     , receiver
                     , _basic_add_crash_branches reliable_rs t)
        else
            ChoiceG(
            sender,
            [ MessageG ({ label = LabelName.of_string "CRASH"; payload = [] } 
                        , sender 
                        , receiver 
                        , _basic_generate_crash_branch sender t
                        |> _basic_add_crash_branches (Set.add reliable_rs sender))
            ; MessageG ( msg
                       , sender
                       , receiver
                       , _basic_add_crash_branches reliable_rs t)])

        | ChoiceG (sender, choices) ->
            (* with the assumption that we do not allow choice of choice of
             * we can assume that after unfolding all branches if they start
             * with a recursion, we are left 
             * only with messages as the first communication *)
            let uncrashed_branches = 
                List.map
                ~f: (apply_to_continuation (_basic_add_crash_branches reliable_rs))
                choices in
            if Set.mem reliable_rs sender
            then ChoiceG(sender, uncrashed_branches)
            else
            let some_branch = 
                match List.hd choices with
                    | None -> EndG
                    | Some branch -> branch in
            let crash_branch = _basic_generate_crash_branch sender some_branch 
                        |> _basic_add_crash_branches (Set.add reliable_rs sender)
            in
            ChoiceG(sender, crash_branch :: uncrashed_branches)

        | MuG (tvar, el, t) -> 
                MuG (tvar, el, _basic_add_crash_branches reliable_rs t)
        | CallG (c, p, pts, t) -> 
                CallG (c, p, pts, _basic_add_crash_branches reliable_rs t)
        | EndG -> EndG
        | other_t -> other_t


(* add crash branch whenever communication from an unreliable role is found *)
let rec _crash_labels
    ~rel_rs ~indices ~rec_t = function
        | MessageG (msg, sender, receiver, t) -> 
            if Set.mem rel_rs sender 
            then 
                MessageG ( msg
                         , sender
                         , receiver
                         , _crash_labels ~rel_rs ~indices ~rec_t t)
            else
                let sender' = indexed_role indices sender in
                let indices' = update_indices indices sender in
                let lcp = Map.of_alist_exn (module RoleName) 
                            [ (sender, sender'); (receiver, sender')] in             
                let csp = Map.of_alist_exn (module RoleName) 
                            [ (sender, Set.singleton (module RoleName) sender')
                            ; (receiver, Set.singleton (module RoleName) sender')
                            ] in
                let crs = Set.singleton (module RoleName) sender in
                let unf = Set.empty (module TypeVariableName) in
                ChoiceG(
                sender,
                [ MessageG ({ label = LabelName.of_string "CRASH"; payload = [] } 
                            , sender' 
                            , receiver 
                            , _crash_branch 
                                ~indices: indices'
                                ~rel_rs ~crs ~lcp ~csp ~rec_t ~unf
                                t)
                ; MessageG ( msg
                           , sender
                           , receiver
                           , _crash_labels ~rel_rs ~indices: indices' ~rec_t t)])

        | ChoiceG (sender, choices) ->
            let indices' = update_indices indices sender in
            let uncrashed_branches = 
                List.map
                ~f: (apply_to_continuation 
                    (_crash_labels ~rel_rs ~indices: indices' ~rec_t))
                choices in
            if Set.mem rel_rs sender
            then ChoiceG(sender, uncrashed_branches)
            else
            let some_branch = 
                match List.hd choices with
                    | None -> EndG
                    | Some branch -> branch in
            let lcp = Map.empty (module RoleName) in
            let csp = Map.empty (module RoleName) in
            let crs = Set.singleton (module RoleName) sender in
            let unf = Set.empty (module TypeVariableName) in
            let crash_branch =
                _crash_branch ~rel_rs ~indices ~crs ~lcp ~csp ~rec_t ~unf some_branch in 
            ChoiceG(sender, crash_branch :: uncrashed_branches)

        | MuG (tvar, el, t) -> 
                let rec_t' = Map.add_exn ~key:tvar ~data:t rec_t in
                MuG (tvar, el, _crash_labels ~rel_rs ~indices ~rec_t:rec_t' t)
        | CallG (c, p, pts, t) -> 
                CallG (c, p, pts, _crash_labels ~rel_rs ~indices ~rec_t t)
        | EndG -> EndG
        | other_t -> other_t

let rec _basic_crash_labels_lgf reliable_rs = function
    | MessageG (msg, sender, receiver, t) -> 
        if Set.mem reliable_rs sender 
        then 
            MessageG ( msg
                     , sender
                     , receiver
                     , _basic_crash_labels_lgf reliable_rs t)
        else
            let aware = Set.of_list (module RoleName) [sender; receiver] in
            ChoiceG(
            sender,
            [ MessageG ({ label = LabelName.of_string "CRASH"; payload = [] } 
                        , sender 
                        , receiver 
                        , _basic_crash_branch_lgf aware sender t
                        |> _basic_crash_labels_lgf (Set.add reliable_rs sender))
            ; MessageG ( msg
                       , sender
                       , receiver
                       , _basic_crash_labels_lgf reliable_rs t)])

        | ChoiceG (sender, choices) ->
            (* with the assumption that we do not allow choice of choice of
             * we can assume that after unfolding all branches if they start
             * with a recursion, we are left 
             * only with messages as the first communication *)
            let uncrashed_branches = 
                List.map
                ~f: (apply_to_continuation (_basic_crash_labels_lgf reliable_rs))
                choices in
            if Set.mem reliable_rs sender
            then ChoiceG(sender, uncrashed_branches)
            else
            let some_branch = 
                match List.hd choices with
                    | None -> EndG
                    | Some branch -> branch in
            let aware = Set.singleton (module RoleName) sender in
            let crash_branch = _basic_crash_branch_lgf aware sender some_branch 
                        |> _basic_crash_labels_lgf (Set.add reliable_rs sender)
            in
            ChoiceG(sender, crash_branch :: uncrashed_branches)

        | MuG (tvar, el, t) -> 
                MuG (tvar, el, _basic_crash_labels_lgf reliable_rs t)
        | CallG (c, p, pts, t) -> 
                CallG (c, p, pts, _basic_crash_labels_lgf reliable_rs t)
        | EndG -> EndG
        | other_t -> other_t


(* introduce crash patterns to global protocols *)
let graceful_failure (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let reliable_rs = global_protocol.value.split_roles.reliable_roles in
    let _rel_rs = Set.of_list (module RoleName) reliable_rs in
    let _indices = 
        participants gtype
        |> Set.to_list 
        |> List.map ~f:(fun r -> (r, 1))
        |> Map.of_alist_exn (module RoleName) in
    let _rec_t = Map.empty (module TypeVariableName) in
    _basic_add_crash_branches _rel_rs gtype
    (* _crash_labels ~rel_rs ~indices gtype ~rec_t *)

module RoleNamePair = struct
    module Pair = struct
        type t = RoleName.t * RoleName.t [@@deriving ord, sexp_of]
    end
    include Pair
    include Comparator.Make (Pair)
end

let local_graceful_failure (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let reliable_rs = global_protocol.value.split_roles.reliable_roles in
    let rel_rs = Set.of_list (module RoleName) reliable_rs in
    let indices = 
        participants gtype
        |> Set.to_list 
        |> List.map ~f:(fun r -> (r, 1))
        |> Map.of_alist_exn (module RoleName) in
    let crs = Set.empty (module RoleName) in
    let cb = Set.empty (module RoleNamePair) in
    let pcp = Map.empty (module RoleName) in
    let aw = Map.empty (module RoleName) in
    let a = Set.empty (module RoleName) in
    let rec_t = Map.empty (module TypeVariableName) in
    _crash_branch_lgf ~rel_rs ~indices ~crs ~cb ~pcp ~aw ~a ~rec_t gtype


module MessageKey = struct
    module T = struct
        type t = Message.message [@@deriving ord, sexp_of]
    end
    include T
    include Comparator.Make(T)
end

type first_r = 
    | Sender of RoleName.t
    | Receiver of RoleName.t

let merge_labels p labels_map = 
    (*q should be consistent across all entries in the map,
      so pick any element from map*)
    let q = match Map.min_elt labels_map with
        | None -> Sender p
        | Some (_, (_, q)) -> q in
    let choices = Map.fold labels_map
        ~init: []
        ~f: (fun ~key: m ~data: (t, r) accum -> 
            match r with 
            | Sender p' -> (MessageG (m, p', p, t) :: accum)
            | Receiver q' -> (MessageG (m, p, q', t) :: accum)) in
    match q with
    | Sender q' -> ChoiceG (q', choices)
    | Receiver _ -> ChoiceG (p, choices)

let rec replace_in_gtype r merged_choices = function
    | MessageG (m, p, q, t) ->
            if RoleName.equal p r || RoleName.equal q r
            then merged_choices
            else MessageG (m, p, q, replace_in_gtype r merged_choices t)

    | ChoiceG (p, choices) -> 
            ( match List.hd choices with
            | Some (MessageG (_, _, q, _)) ->
                if RoleName.equal p r || RoleName.equal q r
                then merged_choices
                else ChoiceG (p, List.map ~f:(replace_in_gtype r merged_choices) choices)
            | _ -> EndG )
    | MuG (tvar, el, t) -> MuG (tvar, el, replace_in_gtype r merged_choices t)
    | _ -> EndG
    
let rec _merge_gtype_on r t = 
    (*helper function*)
    let rec labels_to_merge = function
        | MessageG (m, p, q, t) ->
            let sender_r = RoleName.equal p r in
            let receiver_r = RoleName.equal q r in

            if sender_r && receiver_r
            then 
                _merge_gtype_on r t |> labels_to_merge
            else if not sender_r && not receiver_r
            then labels_to_merge t
            else
                (* first role that communicates with the role we are merging *) 
                let first_r = if sender_r 
                              then Receiver q 
                              else Sender p in
                Map.singleton (module MessageKey) m (_merge_gtype_on r t, first_r)

        | ChoiceG (_, choices) ->
            List.fold choices
                ~init: (Map.empty (module MessageKey))
                ~f: (fun accum t -> 
                    Map.merge_skewed accum (labels_to_merge t)
                        ~combine: (fun ~key: _ t1 _ -> t1))
        | MuG (_, _, t) -> labels_to_merge t
        | _ -> Map.empty (module MessageKey) 
    in
    match t with
    | MessageG (m, p, q, t) ->
        if RoleName.equal p r && RoleName.equal q r
        then _merge_gtype_on r t
        else MessageG (m, p, q, _merge_gtype_on r t)

    | ChoiceG (p, choices) ->
        ( match List.hd choices with
        | Some (MessageG (_, _, q, t)) ->
            if RoleName.equal p r && RoleName.equal q r
            then 
                (* 1. merge on one choice
                   2. from all choices find first interaction of r with 
                some other role and save messages 
                   3. merge them
                   4. append them in the merged choice where
                they are supposed to be
                i.e. first interaction in which r is involved *)
                let merged_t = _merge_gtype_on r t in
                let labels_map = labels_to_merge (ChoiceG (p, choices)) in

                if Map.is_empty labels_map
                then merged_t
                else
                    let merged_choices = merge_labels p labels_map in
                    replace_in_gtype r merged_choices merged_t
            else ChoiceG (p, List.map ~f:(_merge_gtype_on r) choices)
        | _ -> EndG )
    | MuG (tvar, el, t) -> MuG (tvar, el, _merge_gtype_on r t)
    | other_t -> other_t


let update_role crashed_rs backups r =
    if Set.mem crashed_rs r
    then match Map.find backups r with
        | Some b -> b
        | None -> r (*this branch will be taken by crashed roles
                      that do not have a backup*)
    else r

let rec _replace crashed_rs backups = function
    | MessageG (m, p, q, t) ->
            let p' = update_role crashed_rs backups p in
            let q' = update_role crashed_rs backups q in
            MessageG (m, p', q', _replace crashed_rs backups t)

    | ChoiceG (p, choices) ->
            let p' = update_role crashed_rs backups p in
            ChoiceG (p', List.map ~f:(_replace crashed_rs backups) choices )

    
    | MuG (tvar, rv, t) -> 
            let tvar' = TypeVariableName.user tvar ^ "f" in
            let tvar' = TypeVariableName.of_string tvar' in
                MuG(tvar', rv, _replace crashed_rs backups t)
    | CallG (caller, protocol, participants, t) -> 
            let caller = update_role crashed_rs backups caller in
            CallG ( caller 
                  , protocol
                  , participants
                  , _replace crashed_rs backups t)
    | TVarG (tv, es, t) -> 
            let tv' = TypeVariableName.user tv ^ "f" in
            let tv' = TypeVariableName.of_string tv' in
            TVarG (tv', es, t)
    | EndG -> EndG

let rec _notify q waiting_rs label init = 
    Set.fold
        ~f: (fun accum r -> 
        let m = 
            { label = LabelName.of_string label ; payload = [] } in 
            MessageG (m, q, r, accum))
        ~init: init 
        waiting_rs 

let rec find_witnesses w rel_rs = function
    | MessageG (_, p, q, t) ->
            let witnesses = find_witnesses w rel_rs t in
            if Set.mem rel_rs p
            then witnesses (*p reliable, no need to check witness*)
            else if Set.mem (senders t) p 
                 then witnesses (*not last comm of unrel role*)
                 else 
                     if Set.mem rel_rs q
                     then Map.add_exn witnesses ~key:p ~data:q
                     else Map.add_exn witnesses ~key:p ~data:w
    | ChoiceG (_, choices) ->
            (*find witnesses from each branch*)
            let witnessess = List.map choices
                ~f: (fun t -> find_witnesses w rel_rs t) in
            (*merge witnesses; 
             *if they are different for the same role,
             *use default witness *)
            List.fold witnessess
                ~init: (Map.empty (module RoleName))
                ~f: (fun accum ws -> 
            Map.merge_skewed accum ws
                ~combine: (fun ~key: _ v1 v2 -> 
                    if RoleName.equal v1 v2 && Set.mem rel_rs v1 then v1 else w) )
    | MuG (_, _, t) -> find_witnesses w rel_rs t
    | CallG (_, _, _, t) -> find_witnesses w rel_rs t
    | _ -> Map.empty (module RoleName)

let rec add_witnesses rel_rs ws = function
    | MessageG (m, p, q, t) ->
            let p_rel = Set.mem rel_rs p in
            let q_rel = Set.mem rel_rs q in
            let cont = add_witnesses rel_rs ws t in
            if not p_rel 
            then 
                let w = Map.find_exn ws p in
                if not q_rel
                then MessageG (m, p, w, MessageG (m, w, q, cont))
                else if RoleName.equal q w
                     then MessageG (m, p, q, cont)
                     else MessageG (m, p, w, MessageG (m, w, q, cont))
            else MessageG(m, p, q, cont)

    | ChoiceG (p, choices) ->
            ChoiceG (p, List.map ~f:(add_witnesses rel_rs ws) choices)
    | MuG (tvar, es, t) -> MuG (tvar, es, add_witnesses rel_rs ws t)
    | CallG (caller, protocol, participants, t) -> 
            CallG ( caller
                  , protocol
                  , participants
                  , add_witnesses rel_rs ws t)
    | other_t -> other_t

let rec append_to_cont to_append = function
    | MessageG (m, p, q, t) -> MessageG (m, p, q, append_to_cont to_append t)
    | ChoiceG (p, choices) -> ChoiceG (p, List.map 
                                        ~f:(append_to_cont to_append) choices)
    | MuG (tvar, el, t) -> MuG (tvar, el, append_to_cont to_append t)
    | CallG (caller, protocol, participants, t) -> 
            CallG ( caller
                  , protocol
                  , participants
                  , append_to_cont to_append t)
    |_ -> to_append

let unaware pcp p = not (Map.mem pcp p)
let aware_of_crashed_r pcp p r = 
     match Map.find pcp p with
                  | None -> false
                  | Some m -> Map.mem m r 

let not_waiting aw p q = 
    Map.fold aw ~init: true
        ~f: (fun ~key:_ ~data acc -> 
            if Set.mem data p 
            then acc && Set.mem data q
            else acc)

let cp_of r' = 
    let r'_str = RoleName.user r' in
    let r'_split = String.split r'_str ~on: '-' in
    List.hd_exn r'_split

(*check if r' is a crash point of r*)
let is_cp_of r' r = 
    let r_str = RoleName.user r in
    let r'_str = cp_of r' in
    String.equal r'_str r_str

(*check if role r should be attached to label sent by p*)
let attach_to_label cb pcp aw p q r =
    let aware_p = aware_of_crashed_r pcp p r in
    if not aware_p then false (*if p is not aware of r, then it can't send info*)
    else
        let cb_r = match Map.find cb r with
                   | None -> Set.empty (module RoleNamePair)
                   | Some s -> s in
        if Set.mem cb_r (p,q) then false (*they communicated about it before*)
        else
            let pcp_p = Map.find_exn pcp p in
            let pcp_p_r = Map.find_exn pcp_p r in
            Set.fold pcp_p_r ~init: false
                ~f: (fun acc r' -> 
                    let aw_r = Map.find_exn aw r' in
                    acc || not (Set.mem aw_r q))

let notify_about cb pcp aw p q = 
     if unaware pcp p then Set.empty (module RoleName)
     else
     let pcp_p = Map.find_exn pcp p in
     let pcp_p_cs = Map.keys pcp_p in
     Set.of_list (module RoleName) pcp_p_cs
     |> Set.filter ~f:(fun r -> attach_to_label cb pcp aw p q r) 

let compute_label m l cb pcp aw p q = 
    if unaware pcp p then LabelName.user m.label
    else
    let notify_abt = notify_about cb pcp aw p q in
    Set.fold notify_abt ~init: l
        ~f: (fun acc r -> acc ^ (RoleName.user r))

let failover_skip cb pcp aw p q = 
    let notify_abt = notify_about cb pcp aw p q in
    Set.is_empty notify_abt && not_waiting aw p q


let update_failover_aw rel_rs indices aw p q = 
    if Set.mem rel_rs p 
    then Map.map aw ~f:(fun s -> if Set.mem s p then Set.add s q else s)
    else 
        let p_indexed = indexed_role indices p in
        let new_entry = Set.of_list (module RoleName) [p ; q] in
        Map.add_exn aw ~key:p_indexed ~data:new_entry

let update_failover_pcp indices crs cb pcp aw p q = 
    if Set.mem crs p
    then 
        if not (aware_of_crashed_r pcp q p)
        then Map.update pcp q
            ~f:(fun m -> match m with
                | None -> Map.singleton (module RoleName) p 
                        (Set.singleton (module RoleName) (indexed_role indices p))
                | Some m' -> Map.add_exn m' ~key:p 
                    ~data:(Set.singleton (module RoleName) (indexed_role indices p)))
        else pcp
    else
        let notify_abt = notify_about cb pcp aw p q in
        Set.fold notify_abt ~init: pcp
            ~f: (fun acc r ->
                let r_cp = Map.fold ~init: (Set.empty (module RoleName))
                    ~f:(fun ~key: r' ~data: s accum -> 
                        if is_cp_of r' r && Set.mem s p
                        then Set.add accum r'
                        else accum)
                    aw in
                Map.update acc q
                    ~f:(fun m -> match m with
                        | None -> Map.singleton (module RoleName) r r_cp
                        | Some m' -> if Map.mem m' r
                                     then m'
                                     else Map.add_exn m' ~key:r ~data:r_cp))


let update_failover_cb crs cb pcp aw p q = 
    if Set.mem crs p
    then if not (aware_of_crashed_r pcp q p)
         then Map.add_exn cb ~key:p 
                ~data: ( [(p,q) ; (q,p)] 
                     |> Set.of_list (module RoleNamePair) )
         else cb
    else 
        let notify_abt = notify_about cb pcp aw p q in
        Set.fold notify_abt ~init: cb
            ~f: (fun acc r -> Map.update acc r
                ~f:(fun s -> match s with
                    | None -> Set.of_list (module RoleNamePair) [(p,q) ; (q,p)]
                    | Some s' -> Set.add s' (p,q) |> flip Set.add (q,p)))


let rec _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp ~aw ~rec_t ~g_res = 
    function
    | MessageG(m, p, q, t) ->
        let early_restart = Set.mem rel_rs p 
                       && Set.mem rel_rs q
                       && Set.diff (senders t) rel_rs |> Set.is_empty in
        if early_restart
        then MessageG(m, p, q, t)
             |>_recovery_protocol ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb 
                                  ~pcp ~aw ~rec_t ~g_res 
        else
        let p_rel = Set.mem rel_rs p in
        let p_crashed = Set.mem crs p in
        let q_crashed = Set.mem crs q in
        let indices' = if not p_rel then update_indices indices p else indices in
        let aw' = update_failover_aw rel_rs indices aw p q in

        if p_rel
        then if unaware pcp p
             then MessageG(m, p, q, _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' 
                                              ~hs ~crs ~cb ~pcp ~aw:aw' ~rec_t ~g_res t)
             else if q_crashed && aware_of_crashed_r pcp p q
             then _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs ~crs ~cb 
                            ~pcp ~aw:aw' ~rec_t ~g_res t
             else if failover_skip cb pcp aw p q
             then _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs ~crs ~cb 
                            ~pcp ~aw:aw' ~rec_t ~g_res t
             else
                let l = "CRASHED_" in
                let label = compute_label m l cb pcp aw p q in
                let m' = { label = LabelName.of_string label ; payload = [] } in
                let pcp' = update_failover_pcp indices crs cb pcp aw p q in
                let cb' = update_failover_cb crs cb pcp aw p q in
                MessageG( m', p, q, 
                          _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs ~crs 
                                    ~cb:cb' ~pcp:pcp' ~aw:aw' ~rec_t ~g_res t) 
        else
        (*p is unreliable*)
        if not p_crashed
        then let safe_branch = 
                let l = "CRASHED_" in
                let label = compute_label m l cb pcp aw p q in
                let m' = { label = LabelName.of_string label ; payload = [] } in
                let pcp' = update_failover_pcp indices crs cb pcp aw p q in
                let cb' = update_failover_cb crs cb pcp aw p q in
                MessageG( m', p, q
                        , _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                              ~crs ~cb:cb' ~pcp:pcp' ~aw:aw' ~rec_t ~g_res t) in
             (*crash p in one branch*)
             let crs' = Set.add crs p in
             let pcp' = update_failover_pcp indices crs' cb pcp aw p q in
             let cb' = update_failover_cb crs' cb pcp aw p q in
             let crash_branch = 
                 MessageG( { label = LabelName.of_string "CRASH"; payload = [] }
                         , p, q
                         , _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                              ~crs:crs' ~cb:cb' ~pcp:pcp' ~aw:aw' ~rec_t ~g_res t) in
             ChoiceG( p, [safe_branch; crash_branch])
        else
            (*p is crashed, check if can skip*)
            if aware_of_crashed_r pcp q p
            then _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                          ~crs ~cb ~pcp ~aw:aw' ~rec_t ~g_res t
            else
                let pcp' = update_failover_pcp indices crs cb pcp aw p q in
                let cb' = update_failover_cb crs cb pcp aw p q in
                MessageG( { label = LabelName.of_string "CRASH"; payload = [] }
                        , p, q
                        , _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                              ~crs ~cb:cb' ~pcp:pcp' ~aw:aw' ~rec_t ~g_res t)
    | ChoiceG (p, choices) ->
        let some_branch = 
            match List.hd choices with
                | None -> EndG
                | Some branch -> branch in
        let q = match some_branch with
            | MessageG (_, _, q, _) -> q
            | _ -> unimpl ~here:[%here] "Choice with non-message branch" in
        let aw' = update_lgf_aw rel_rs indices aw p q in
        let indices' = if not (Set.mem rel_rs p)
                       then update_indices indices p 
                       else indices in
        if Set.mem rel_rs p 
        then if unaware pcp p
             then ChoiceG(p, List.map choices
                    ~f: (apply_to_continuation
                        (_failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs ~crs 
                                   ~cb ~pcp ~aw:aw' ~rec_t ~g_res))) 
             else _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp 
                           ~aw ~rec_t ~g_res some_branch
        else if Set.mem crs p
        then _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp 
                      ~aw ~rec_t ~g_res some_branch
        else 
            let safe_branches = 
                if unaware pcp p
                then List.map choices
                    ~f: (apply_to_continuation 
                        (_failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs ~crs 
                                   ~cb ~pcp ~aw:aw' ~rec_t ~g_res))
                else 
                    ( match some_branch with
                    | MessageG (m, p, q, t) ->
                    (*same as for reliable message in MessageG (...)*)
                     if Set.mem crs q && aware_of_crashed_r pcp p q
                     then [ _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                                      ~crs ~cb ~pcp ~aw:aw' ~rec_t ~g_res t ]
                     else if failover_skip cb pcp aw p q
                     then [ _failover ~rel_rs ~bs ~dw ~ws ~indices:indices' ~hs
                                      ~crs ~cb ~pcp ~aw:aw' ~rec_t ~g_res t ]
                     else
                        let l = "CRASHED_" in
                        let label = compute_label m l cb pcp aw p q in
                        let m' = { label = LabelName.of_string label ; payload = [] } in
                        let pcp' = update_failover_pcp indices crs cb pcp aw p q in
                        let cb' = update_failover_cb crs cb pcp aw p q in
                            [ MessageG( m', p, q, 
                                    _failover ~rel_rs ~bs ~dw ~ws 
                                              ~indices:indices' ~hs ~crs ~cb:cb' 
                                              ~pcp:pcp' ~aw:aw' ~rec_t ~g_res t) ]

                    | _ -> unimpl ~here:[%here] "Choice with non-message branch")
                    in
            let crash_branch =
                let crs' = Set.add crs p in
                 _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs:crs' ~cb
                           ~pcp ~aw ~rec_t ~g_res some_branch in
            ChoiceG(p, crash_branch :: safe_branches)
    | MuG (tvar, el, t) -> 
            let rec_t' = Set.add rec_t tvar in
            MuG (tvar, el, _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs 
                                     ~cb ~pcp ~aw ~rec_t:rec_t' ~g_res t)
    | CallG (caller, protocol, participants, t) -> 
            CallG (caller, protocol, participants, 
                   _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp 
                             ~aw ~rec_t ~g_res t)
    | other_t -> _recovery_protocol ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp 
                                   ~aw ~rec_t ~g_res other_t

and _recovery_protocol ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb ~pcp ~aw ~rec_t ~g_res t = 
    let hs' = Set.union hs crs in
    let cont = if Set.is_empty crs 
               then t 
               else let restart = _replace crs bs g_res in
                    let crs' = Set.empty (module RoleName) in
                    let cb' = Map.empty (module RoleName) in
                    let pcp' = Map.empty (module RoleName) in
                    let aw' = Map.empty (module RoleName) in
                    _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs:hs'
                              ~crs:crs' ~cb:cb' ~pcp:pcp' ~aw:aw' 
                              ~rec_t ~g_res:restart restart in
    (*all witnesses send messages to default witness dw about 
     their corresponding unreliable role*)
    let init = if Set.is_empty crs then t else cont in
    let senders = senders g_res in
    let pt = participants g_res in
    let notify_abt = Set.diff senders rel_rs in
    let safe_rs = Set.diff notify_abt crs in
    let (to_dw, _cb', _pcp', _aw') = Set.fold notify_abt
        ~init: (EndG, cb, pcp, aw)
        ~f: (fun accum p -> 
            let (cont_a, cb_a, pcp_a, aw_a) = accum in
            let w = Map.find_exn ws p in
            if RoleName.equal w dw
            then (cont_a, cb_a, pcp_a, aw_a)
            else
            let aw' = update_failover_aw rel_rs indices aw_a w dw in
            let pcp' = update_failover_pcp indices crs cb_a pcp_a aw_a w dw in
            let cb' = update_failover_cb crs cb_a pcp_a aw_a p w in
            if failover_skip cb pcp aw p w
             then (*no crashed roles to notify about*)
                 if Set.mem safe_rs p
                 then (*need to send safe message*) 
                     let label = LabelName.of_string ("SAFE_" ^ RoleName.user p) in
                     ( MessageG( { label = label; payload = [] }
                               , p, w, cont_a)
                     , cb', pcp', aw' )
                 else (cont_a, cb', pcp', aw')
             else
                let l = "CRASHED_" in
                let dummy_m = { label = LabelName.of_string l ; payload = [] } in
                let label = compute_label dummy_m l cb_a pcp_a aw_a w dw in
                let m' = { label = LabelName.of_string label ; payload = [] } in
                ( MessageG( m', w, dw, cont_a), cb', pcp', aw' ) ) in

    (*default witness send messages to other roles*)
    let dw_to_rs = 
        if Set.is_empty crs 
        then (*send only safe messages*)
            let unrel_rs = Set.diff senders rel_rs in
            if Set.is_empty unrel_rs
            then init (*if there are no unreliable roles, do not send safe msgs*)
            else
            let ws_values = Map.data ws |> Set.of_list (module RoleName) in
            (*witnesses already know it is safe since they sent the safe messages*)
            let notify = Set.diff pt ws_values in
            (*remove default witness*)
            let notify = Set.remove notify dw in
            (*send messages to backups of unreliable senders*)
            let bs_values = Map.fold bs ~init: (Set.empty (module RoleName))
                ~f: (fun ~key: r ~data: b accum -> 
                    if Set.mem unrel_rs r
                    then Set.add accum b
                    else accum) in
            let notify = Set.union notify bs_values in
            (*if there is only one unreliable role, no need to send back
             safe message to it*)
            let notify = if Set.length safe_rs = 1
                         then Set.choose_exn safe_rs |> Set.remove notify
                         else notify in
            let m = { label = LabelName.of_string "SAFE"; payload = [] } in
        Set.fold notify
        ~init: init
        ~f: (fun accum p -> MessageG(m, dw, p, accum))
        else (*there is at least one crashed role*)
            (*send messages to crashed roles' backups about 
             all crashes, including previous runs*)
            let dw_to_bs = Set.fold crs
                        ~init: init
                        ~f: (fun accum r -> 
                            let b = Map.find_exn bs r in
                            let label = Set.fold hs'
                                ~init: "CRASHED_"
                                ~f: (fun accum r' -> accum ^ RoleName.user r') in
                            let m = { label = LabelName.of_string label 
                                    ; payload = [] } in
                            MessageG(m, dw, b, accum) )
            in
            (*do not send messages to crashed roles*)
            let notify = Set.diff pt crs in
            Set.fold notify
                ~init: dw_to_bs
                ~f: (fun accum p -> 
                    let l = "CRASHED_" in
                    let dummy_m = { label = LabelName.of_string l ; payload = [] } in
                    let label = compute_label dummy_m l cb pcp aw dw p in
                    let m' = { label = LabelName.of_string label ; payload = [] } in
                    if failover_skip _cb' _pcp' _aw' dw p
                    then accum
                    else MessageG(m', dw, p, accum) ) in
    append_to_cont dw_to_rs to_dw
            



let failover (global_protocol : global_protocol) = 
    let open! Syntax in
    let gtype = of_protocol global_protocol in
    let rel_rs = global_protocol.value.split_roles.reliable_roles in
    let rel_rs = Set.of_list (module RoleName) rel_rs in
    let dw = match global_protocol.value.split_roles.notifier with
            | None -> RoleName.of_string "DUMMY"
            | Some r -> r in
    let backups = global_protocol.value.split_roles.backups_map in
    let bs = 
        match Map.of_alist (module RoleName) backups with
        | `Ok bckps -> bckps
        (*TODO: raise error for duplicate*)
        | `Duplicate_key _  -> Map.empty(module RoleName) in
    let ws = find_witnesses dw rel_rs gtype in
    let gtype' = add_witnesses rel_rs ws gtype in
    let indices = 
        participants gtype'
        |> Set.to_list 
        |> List.map ~f:(fun r -> (r, 1))
        |> Map.of_alist_exn (module RoleName) in
    let hs = Set.empty (module RoleName) in
    let crs = Set.empty (module RoleName) in
    let cb = Map.empty (module RoleName) in
    let pcp = Map.empty (module RoleName) in
    let aw = Map.empty (module RoleName) in
    let rec_t = Set.empty (module TypeVariableName) in
    _failover ~rel_rs ~bs ~dw ~ws ~indices ~hs ~crs ~cb 
              ~pcp ~aw ~rec_t ~g_res:gtype' gtype'
