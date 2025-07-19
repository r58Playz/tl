use crate::errors::ParseError;
use crate::parser::HTMLVersion;
use crate::parser::NodeHandle;
use crate::ParserOptions;
use crate::{Node, Parser};
use std::marker::PhantomData;

/// VDom represents a [Document Object Model](https://developer.mozilla.org/en/docs/Web/API/Document_Object_Model)
///
/// It is the result of parsing an HTML document.
/// Internally it is only a wrapper around the [`Parser`] struct, in which all of the HTML tags are stored.
/// Many functions of the public API take a reference to a [`Parser`] as a parameter to resolve [`NodeHandle`]s to [`Node`]s.
#[derive(Debug)]
pub struct VDom<'a> {
    /// Internal parser
    parser: Parser<'a>,
}

impl<'a> From<Parser<'a>> for VDom<'a> {
    fn from(parser: Parser<'a>) -> Self {
        Self { parser }
    }
}

impl<'a> VDom<'a> {
    /// Returns a reference to the underlying parser
    #[inline]
    pub fn parser(&self) -> &Parser<'a> {
        &self.parser
    }

    /// Returns a mutable reference to the underlying parser
    #[inline]
    pub fn parser_mut(&mut self) -> &mut Parser<'a> {
        &mut self.parser
    }

    /// Returns a slice of *all* the elements in the HTML document
    ///
    /// The difference between `children()` and `nodes()` is that children only returns the immediate children of the root node,
    /// while `nodes()` returns all nodes, including nested tags.
    ///
    /// # Order
    /// The order of the returned nodes is the same as the order of the nodes in the HTML document.
    pub fn nodes(&self) -> &[Node<'a>] {
        &self.parser.tags
    }

    /// Returns a mutable slice of *all* the elements in the HTML document
    ///
    /// The difference between `children()` and `nodes()` is that children only returns the immediate children of the root node,
    /// while `nodes()` returns all nodes, including nested tags.
    pub fn nodes_mut(&mut self) -> &mut [Node<'a>] {
        &mut self.parser.tags
    }

    /// Returns the topmost subnodes ("children") of this DOM
    pub fn children(&self) -> &[NodeHandle] {
        &self.parser.ast
    }

    /// Returns a mutable reference to the topmost subnodes ("children") of this DOM
    pub fn children_mut(&mut self) -> &mut [NodeHandle] {
        &mut self.parser.ast
    }

    /// Returns the HTML version.
    /// This is determined by the `<!DOCTYPE>` tag
    pub fn version(&self) -> Option<HTMLVersion> {
        self.parser.version
    }
}

/// A RAII guarded version of VDom
///
/// The input string is freed once this struct goes out of scope.
/// The only way to construct this is by calling `parse_owned()`.
#[derive(Debug)]
pub struct VDomGuard {
    /// Wrapped VDom instance
    dom: VDom<'static>,
    /// The leaked input string that is referenced by self.dom
    _s: RawString,
    /// PhantomData for self.dom
    _phantom: PhantomData<&'static str>,
}

unsafe impl Send for VDomGuard {}
unsafe impl Sync for VDomGuard {}

impl VDomGuard {
    /// Parses the input string
    pub(crate) fn parse(input: String, options: ParserOptions) -> Result<VDomGuard, ParseError> {
        let input = RawString::new(input);

        let ptr = input.as_ptr();

        let input_ref: &'static str = unsafe { &*ptr };

        // Parsing will either:
        // a) succeed, and we return a VDom instance
        //    that, when dropped, will free the input string
        // b) fail, and we return a ParseError
        //    and `RawString`s destructor will run and deallocate the string properly
        let mut parser = Parser::new(input_ref, options);
        parser.parse()?;

        Ok(Self {
            _s: input,
            dom: VDom::from(parser),
            _phantom: PhantomData,
        })
    }
}

impl VDomGuard {
    /// Returns a reference to the inner DOM.
    ///
    /// The lifetime of the returned `VDom` is bound to self so that elements cannot outlive this `VDomGuard` struct.
    pub fn get_ref<'a>(&'a self) -> &'a VDom<'a> {
        &self.dom
    }

    /// Returns a mutable reference to the inner DOM.
    ///
    /// The lifetime of the returned `VDom` is bound to self so that elements cannot outlive this `VDomGuard` struct.
    pub fn get_mut_ref<'a, 'b: 'a>(&'b mut self) -> &'b VDom<'a> {
        &mut self.dom
    }
}

#[derive(Debug)]
struct RawString(*mut str);

impl RawString {
    pub fn new(s: String) -> Self {
        Self(Box::into_raw(s.into_boxed_str()))
    }

    pub fn as_ptr(&self) -> *mut str {
        self.0
    }
}

impl Drop for RawString {
    fn drop(&mut self) {
        // SAFETY: the pointer is always valid because `RawString` can only be constructed through `RawString::new()`
        unsafe {
            drop(Box::from_raw(self.0));
        };
    }
}
