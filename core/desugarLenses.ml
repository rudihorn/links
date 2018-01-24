
class desugar_lenses env = 
object (o : 'self_type)
    inherit (TransformSugar.transform env) as super

    method! phrasenode : Sugartypes.phrasenode -> ('self_type * Sugartypes.phrasenode * Types.datatype) = function
    | `LensKeysLit (t, keys, sort) as e -> 
        let _ = Debug.print "test" in
        super#phrasenode e
    | e -> super#phrasenode e 
end

let desugar_lenses env = ((new desugar_lenses env) : desugar_lenses :> TransformSugar.transform)
