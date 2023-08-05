use eval;
use monaco::api::TextModel;
use std::io::BufWriter;
use yew::{html, Component, Context, Html};
mod editor;
extern crate core;

const TEST_CASE_1_MAIN: &str = std::include_str!("../../milestones/1/main.ch");
const TEST_CASE_1_ADVANCED: &str = std::include_str!("../../milestones/1/advanced.ch");
const TEST_CASE_3_MAIN: &str = std::include_str!("../../milestones/3/main.ch");
const TEST_CASE_3_ADVANCED: &str = std::include_str!("../../milestones/3/advanced.ch");
// const TEST_CASE_3_OPERATION: &str = std::include_str!("../../milestones/3/operation.ch");
const TEST_CASE_4_MAIN: &str = std::include_str!("../../milestones/4/main.ch");
const TEST_CASE_5_MAIN: &str = std::include_str!("../../milestones/5/main.ch");
const TEST_CASE_5_EXPLICIT: &str = std::include_str!("../../milestones/5/explicit.ch");
const TEST_CASE_5_FLOAT: &str = std::include_str!("../../milestones/5/float.ch");
// const TEST_CASE_5_HARD: &str = std:  :include_str!("../../milestones/5/hard.ch");
const TEST_CASE_5_SEVERAL: &str = std::include_str!("../../milestones/5/several.ch");
const TEST_CASE_6_SCOPE: &str = std::include_str!("../../milestones/6/scope.ch");
// const TEST_CASE_6_MAIN: &str = std::include_str!("../../milestones/6/main.ch");

fn run(code: &str) -> Result<String, String> {
    match core::build(&code) {
        Err(error) => {
            if let Some(line) = code.lines().nth(error.location.line as usize - 1) {
                Err(format!("{}", line))
            } else {
                Err("Unknown error".to_owned())
            }
        }
        Ok(bytecode) => {
            let mut buf = BufWriter::new(Vec::new());
            if let Err(msg) = eval::evaluate(&bytecode, &mut buf) {
                Err(format!("Runtime Error: {}", msg))
            } else {
                let bytes = buf.into_inner().unwrap();
                let string = String::from_utf8(bytes).unwrap();
                Ok(string)
            }
        }
    }
}

pub struct Msg {
    eval_id: usize,
}

struct Sample {
    input: TextModel,
    output: String,
    title: String,
    desc: String,
}

impl Sample {
    pub fn new(title: &str, desc: &str, input: &str) -> Self {
        Self {
            input: TextModel::create(&input, None, None).unwrap(),
            output: "".to_owned(),
            title: title.to_owned(),
            desc: desc.to_owned(),
        }
    }
}

struct App {
    samples: Vec<Sample>,
}
impl Component for App {
    type Message = Msg;
    type Properties = ();

    fn create(_context: &Context<Self>) -> Self {
        Self {
            samples: vec![
                Sample::new("Piping", "Chop supports pipes known from bash.", TEST_CASE_1_MAIN),
                Sample::new("Brackets", "Brackets are often optional.", TEST_CASE_1_ADVANCED),
                // Sample::new("Operators", "", TEST_CASE_3_OPERATION),
                Sample::new("Terms", "", TEST_CASE_3_MAIN),
                Sample::new("Concise Brackets", "", TEST_CASE_3_ADVANCED),
                Sample::new("Variables", "", TEST_CASE_4_MAIN),
                Sample::new("Primitive Types", "", TEST_CASE_5_MAIN),
                Sample::new("Explicit Casts", "", TEST_CASE_5_EXPLICIT),
                // Sample::new("Nested Function Calls ", "", TEST_CASE_5_HARD),
                Sample::new("Floating Numbers", "", TEST_CASE_5_FLOAT),
                Sample::new("Casts of Variables", "", TEST_CASE_5_SEVERAL),
                Sample::new("Scopes", "", TEST_CASE_6_SCOPE),
            ],
        }
    }

    fn update(&mut self, _ctx: &Context<Self>, msg: Self::Message) -> bool {
        if msg.eval_id < self.samples.len() {
            self.samples[msg.eval_id].output =
                run(&self.samples[msg.eval_id].input.get_value()).unwrap_or("Error".to_owned());
            true
        } else {
            false
        }
    }

    fn view(&self, ctx: &Context<Self>) -> Html {
        let samples = self
            .samples
            .iter()
            .enumerate()
            .map(|(i, sample)| {
                html!(
                    <div class={"example-block"}>
                        <h2>{&sample.title}</h2>
                        <p>{&sample.desc}</p>
                        <div>
                            <editor::App code={sample.input.to_owned()}
                            />
                            <button onclick={ctx.link().callback(move |_| Msg{eval_id: i})}>
                                { "eval" }
                            </button>
                        </div>
                        <div class={"output"}>
                            <span>{&sample.output}</span>
                        </div>
                    </div>
                )
            })
            .collect::<Html>();

        html! {
        <div class={"main"}>
            <h1>{"Chop by Examples"}</h1>
            {samples}
        </div>
        }
    }
}

fn main() {
    wasm_logger::init(wasm_logger::Config::default());
    yew::Renderer::<App>::new().render();
}
