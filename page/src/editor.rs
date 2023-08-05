use monaco::{
    api::{CodeEditorOptions, TextModel},
    sys::editor::BuiltinTheme,
    yew::CodeEditor,
};
use std::rc::Rc;
use yew::{html, Component, Context, Html, Properties};

fn get_options(code: &str) -> CodeEditorOptions {
    CodeEditorOptions::default()
        .with_language("rust".to_owned())
        .with_value(code.to_owned())
        .with_builtin_theme(BuiltinTheme::VsDark)
        .with_scroll_beyond_last_line(false)
        .with_automatic_layout(true)
}

#[derive(Clone, Debug, PartialEq, Properties)]
pub struct Props {
    pub code: TextModel,
}

pub struct App {
    options: Rc<CodeEditorOptions>,
}
impl Component for App {
    type Message = ();
    type Properties = Props;

    fn create(context: &Context<Self>) -> Self {
        let code = &context.props().code;
        Self {
            options: Rc::new(get_options(&code.get_value())),
        }
    }

    fn changed(&mut self, context: &Context<Self>, old_props: &Self::Properties) -> bool {
        context.props().code.get_value() != old_props.code.get_value()
    }

    fn view(&self, _context: &Context<Self>) -> Html {
        html! {
            <CodeEditor classes={"editor"} model={_context.props().code.clone()} options={ self.options.to_sys_options() } />
        }
    }
}
