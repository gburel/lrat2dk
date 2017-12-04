open Asttypes
open Parsetree
open Ast_mapper

let remove_noopt_mapper argv =
  { default_mapper with
    expr = fun mapper expr ->
      match expr with
      | { pexp_attributes = [{ txt = "noopt" }, _] } ->
        [%expr ()]
      | other -> default_mapper.expr mapper other; }

let () =
  register "ppx_remove_debug" remove_noopt_mapper
