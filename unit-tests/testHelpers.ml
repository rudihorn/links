open OUnit2

let verbose_opt = Conf.make_bool "v" false "Print verbose information."

module Helpers = struct 
    let print test_ctx message =
        if verbose_opt test_ctx then
            print_endline message
        else
            ()
end

