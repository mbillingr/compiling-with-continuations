pub mod kinds;
pub mod substitutions;
pub mod types;
pub mod unification;

pub type Result<T> = std::result::Result<T, String>;

type Int = usize;
type Id = String;
