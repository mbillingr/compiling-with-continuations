pub mod kinds;
pub mod predicates;
pub mod qualified;
pub mod scheme;
pub mod substitutions;
pub mod types;
pub mod unification;

pub type Result<T> = std::result::Result<T, String>;

type Int = usize;
type Id = String;
