use std::cmp::Ordering;

#[derive(Debug, PartialEq)]
pub struct CompilerError {
    pub location: Location,
    pub msg: String,
}

pub trait ToCompilerError {
    type OkType;
    fn convert(self, location: &Location) -> Result<Self::OkType, CompilerError>;
}

impl<T> ToCompilerError for Result<T, String> {
    type OkType = T;
    fn convert(self, location: &Location) -> Result<Self::OkType, CompilerError> {
        match self {
            Ok(t) => Ok(t),
            Err(msg) => Err(CompilerError {
                msg,
                location: location.clone(),
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Location {
    pub line: u32,
    pub begin: usize,
    pub end: usize,
}

impl PartialOrd for Location {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.line != other.line {
            self.line.partial_cmp(&other.line)
        } else {
            self.begin.partial_cmp(&other.begin)
        }
    }
}

impl Location {
    pub fn to_error(&self, msg: String) -> CompilerError {
        CompilerError {
            location: self.clone(),
            msg,
        }
    }
}

pub trait Locatable {
    fn get_loc(&self) -> &Location;
}

impl CompilerError {
    pub fn print(&self, filename: &str) {
        eprintln!(
            "{}:{}:{}",
            filename, self.location.line, self.location.begin
        );
        eprintln!("{}", self.msg);
    }

    pub fn global(msg: &str) -> CompilerError {
        CompilerError {
            location: Default::default(),
            msg: msg.to_string(),
        }
    }

    pub fn from_token<T>(token: &dyn Locatable, msg: String) -> CompilerError {
        CompilerError {
            location: token.get_loc().clone(),
            msg,
        }
    }
}
