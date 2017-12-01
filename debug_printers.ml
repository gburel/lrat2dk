open Ptset
open Lrat_types

let print_ptset ppf t =
  Format.fprintf ppf "@[{";
  Ptset.iter (Format.fprintf ppf "%i;@ ") t;
  Format.fprintf ppf "}@]"

let print_rup ppf l = 
  Format.fprintf ppf "@[[";
  List.iter (Format.fprintf ppf "%a;@ " pp_id) l;
  Format.fprintf ppf "]@]"
    
let print_idmap ppf (m : (id list) IdMap.t) =
  Format.fprintf ppf "@[{";
  IdMap.iter (fun i r ->
    Format.fprintf ppf "%a -> %a;@ "
      pp_id i
      print_rup r
  ) m;
  Format.fprintf ppf "}@]"
  
