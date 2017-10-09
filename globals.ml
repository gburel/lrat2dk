let clause_map = Hashtbl.create 1001

let dedukti_out =
  let oc = open_out "dedukti_out.dk" in
  Format.formatter_of_out_channel oc
    
