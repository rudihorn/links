module Debug = Debug

module Column = Column
module Sort = Lens_sort
module Fun_dep = Lens_fun_dep
module Alias = Alias

module Phrase = struct
  include Lens_phrase

  module Sugar = Lens_phrase_sugar

  module Type = Lens_phrase_type

  module Typesugar = Lens_phrase_typesugar
end

module Operators = Lens_operators

module Type = Lens_type
module Value = Lens_value
module Database = Lens_database
module Statistics = Lens_statistics
module Sorted_records = Lens_sorted_records


module Helpers = struct
  module Classic = LensHelpersClassic
  module Incremental = LensHelpersIncremental
end

module Utility = Lens_utility