open! Core_kernel
open Syntax
open Err

type global_type =
  | Message of message * name * name * global_type
  | Mu of name * global_type
  | TVar of name
  | ChoiceT of name * global_type list
  | End
[@@deriving show]

let unimpl desc = UnImplemented desc |> raise

let global_type_of_protocol global_protocol =
  let {value= {name; roles; interactions; _}; _} = global_protocol in
  let has_global_recursion = ref false in
  let global_recursion_name = "__" ^ name in
  let assert_empty l =
    if not @@ List.is_empty l then unimpl "Non tail-recursive protocol"
  in
  let check_role r =
    if not @@ List.mem roles r ~equal:( = ) then unimpl "Unbound role name"
  in
  let rec conv_interactions rec_names
      (interactions : global_interaction list) =
    match interactions with
    | [] -> End
    | {value; _} :: rest -> (
      match value with
      | MessageTransfer {message; from_role; to_roles; _} ->
          if List.length to_roles <> 1 then
            unimpl "Sending to multiple roles" ;
          let to_role = Option.value_exn (List.hd to_roles) in
          check_role from_role ;
          check_role to_role ;
          Message
            (message, from_role, to_role, conv_interactions rec_names rest)
      | Recursion (rname, interactions) ->
          if List.mem rec_names rname ~equal:( = ) then
            unimpl "Alpha convert recursion names"
          else assert_empty rest ;
          Mu (rname, conv_interactions (rname :: rec_names) interactions)
      | Continue name ->
          if List.mem rec_names name ~equal:( = ) then (
            assert_empty rest ; TVar name )
          else unimpl "Error message for Unbound TVar"
      | Choice (role, interactions_list) ->
          assert_empty rest ;
          check_role role ;
          ChoiceT
            ( role
            , List.map ~f:(conv_interactions rec_names) interactions_list )
      | Do (name_, _, roles_, _)
        when name = name_ && List.equal ( = ) roles roles_ ->
          has_global_recursion := true ;
          assert_empty rest ;
          TVar global_recursion_name
      | Do _ -> unimpl "handle `do` that are non-identical to top level"
      | _ -> unimpl "Other Scribble constructs" )
  in
  let converted = conv_interactions [global_recursion_name] interactions in
  let converted =
    if !has_global_recursion then Mu (global_recursion_name, converted)
    else converted
  in
  converted
