open Ppxlib

let remove_noopt_mapper =
  object
    inherit Ppxlib.Ast_traverse.map as super

    method! expression e =
      match e with
      | { pexp_attributes = [{ attr_name = { txt = "noopt"; _ }; attr_loc = loc ; _ }] ; _ } ->
         [%expr ()]
      | _ -> super#expression e (* Continue traversing inside the node *)
  end


let () =
  Ppxlib.Driver.register_transformation
    "ppx_remove_debug"
    ~impl:remove_noopt_mapper#structure
    ~intf:remove_noopt_mapper#signature

let () = Ppxlib.Driver.run_as_ppx_rewriter ()
