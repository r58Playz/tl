use crate::{
    inline::{hashmap::InlineHashMap, vec::InlineVec},
    Bytes, InnerNodeHandle,
};
use std::borrow::Cow;

use super::{handle::NodeHandle, Parser};

const INLINED_ATTRIBUTES: usize = 2;
const INLINED_SUBNODES: usize = 2;
const HTML_VOID_ELEMENTS: [&str; 16] = [
    "area", "base", "br", "col", "command", "embed", "hr", "img", "input", "keygen", "link",
    "meta", "param", "source", "track", "wbr",
];

/// The type of map for attributes
pub type Attributes<'a> = InlineHashMap<Bytes<'a>, Option<Bytes<'a>>, INLINED_ATTRIBUTES>;

/// The type of vector for children of an HTML tag
pub type RawChildren = InlineVec<NodeHandle, INLINED_SUBNODES>;

/// Represents a single HTML element
#[derive(Debug, Clone)]
pub struct HTMLTag<'a> {
    pub(crate) _name: Bytes<'a>,
    pub(crate) _attributes: Attributes<'a>,
    pub(crate) _children: RawChildren,
    pub(crate) _raw: Bytes<'a>,
	pub(crate) _inner: Bytes<'a>,
}

impl<'a> HTMLTag<'a> {
    /// Creates a new HTMLTag
    #[inline(always)]
    pub(crate) fn new(
        name: Bytes<'a>,
        attr: Attributes<'a>,
        children: InlineVec<NodeHandle, INLINED_SUBNODES>,
        raw: Bytes<'a>,
		inner: Bytes<'a>,
    ) -> Self {
        Self {
            _name: name,
            _attributes: attr,
            _children: children,
            _raw: raw,
			_inner: inner,
        }
    }

    /// Returns a wrapper around the children of this HTML tag
    #[inline]
    pub fn children(&self) -> Children<'a, '_> {
        Children(self)
    }

    /// Returns a mutable wrapper around the children of this HTML tag.
    pub fn children_mut(&mut self) -> ChildrenMut<'a, '_> {
        ChildrenMut(self)
    }

    /// Returns the name of this HTML tag
    #[inline]
    pub fn name(&self) -> &Bytes<'a> {
        &self._name
    }

    /// Returns a mutable reference to the name of this HTML tag
    #[inline]
    pub fn name_mut(&mut self) -> &mut Bytes<'a> {
        &mut self._name
    }

    /// Returns attributes of this HTML tag
    #[inline]
    pub fn attributes(&self) -> &Attributes<'a> {
        &self._attributes
    }

    /// Returns a mutable reference to the attributes of this HTML tag
    #[inline]
    pub fn attributes_mut(&mut self) -> &mut Attributes<'a> {
        &mut self._attributes
    }

    /// Returns the contained markup
    pub fn inner_html<'p>(&'p self) -> &Bytes<'a> {
        &self._inner
    }

    /// Returns the raw HTML of this tag.
    /// This is a cheaper version of `HTMLTag::inner_html` if you never mutate any nodes.
    ///
    /// **Note:** Mutating this tag does *not* re-compute the HTML representation of this tag.
    /// This simply returns a reference to the substring.
    pub fn raw(&self) -> &Bytes<'a> {
        &self._raw
    }

    /// Returns the boundaries/position `(start, end)` of this HTML tag in the source string.
    ///
    /// # Example
    /// ```
    /// let source = "<p><span>hello</span></p>";
    /// let dom = tl::parse(source, Default::default()).unwrap();
    /// let parser = dom.parser();
    /// let span = dom.nodes().iter().filter_map(|n| n.as_tag()).find(|n| n.name() == "span").unwrap();
    /// let (start, end) = span.boundaries(parser);
    /// assert_eq!((start, end), (3, 20));
    /// assert_eq!(&source[start..=end], "<span>hello</span>");
    /// ```
    pub fn boundaries(&self, parser: &Parser<'a>) -> (usize, usize) {
        let raw = self._raw.as_bytes();
        let input = parser.stream.data().as_ptr();
        let start = raw.as_ptr();
        let offset = start as usize - input as usize;
        let end = offset + raw.len() - 1;
        (offset, end)
    }

    /// Returns the contained text of this element, excluding any markup.
    /// Equivalent to [Element#innerText](https://developer.mozilla.org/en-US/docs/Web/API/HTMLElement/innerText) in browsers.
    /// This function may not allocate memory for a new string as it can just return the part of the tag that doesn't have markup.
    /// For tags that *do* have more than one subnode, this will allocate memory
    pub fn inner_text<'p>(&self, parser: &'p Parser<'a>) -> Cow<'p, str> {
        let len = self._children.len();

        if len == 0 {
            // If there are no subnodes, we can just return a static, empty, string slice
            return Cow::Borrowed("");
        }

        let first = self._children[0].get(parser).unwrap();

        if len == 1 {
            match &first {
                Node::Tag(t) => return t.inner_text(parser),
                Node::Raw(e) => return e.as_utf8_str(),
                Node::Comment(_) => return Cow::Borrowed(""),
            }
        }

        // If there are >1 nodes, we need to allocate a new string and push each inner_text in it
        // TODO: check if String::with_capacity() is worth it
        let mut s = String::from(first.inner_text(parser));

        for &id in self._children.iter().skip(1) {
            let node = id.get(parser).unwrap();

            match &node {
                Node::Tag(t) => s.push_str(&t.inner_text(parser)),
                Node::Raw(e) => s.push_str(&e.as_utf8_str()),
                Node::Comment(_) => { /* no op */ }
            }
        }

        Cow::Owned(s)
    }

    /// Calls the given closure with each tag as parameter
    ///
    /// The closure must return a boolean, indicating whether it should stop iterating
    /// Returning `true` will break the loop
    pub fn find_node<F>(&self, parser: &Parser<'a>, f: &mut F) -> Option<NodeHandle>
    where
        F: FnMut(&Node<'a>) -> bool,
    {
        for &id in self._children.iter() {
            let node = id.get(parser).unwrap();

            if f(node) {
                return Some(id);
            }
        }
        None
    }
}

/// A thin wrapper around the children of [`HTMLTag`]
#[derive(Debug, Clone)]
pub struct Children<'a, 'b>(&'b HTMLTag<'a>);

impl<'a, 'b> Children<'a, 'b> {
    /// Returns the topmost, direct children of this tag.
    ///
    /// # Example
    /// ```
    /// let dom = tl::parse(r#"
    ///     <div id="a">
    ///         <div id="b">
    ///             <span>Hello</span>
    ///             <span>World</span>
    ///             <span>.</span>
    ///         </div>
    ///     </div>
    /// "#, Default::default()).unwrap();
    ///
    /// let a = dom.get_element_by_id("a")
    ///     .unwrap()
    ///     .get(dom.parser())
    ///     .unwrap()
    ///     .as_tag()
    ///     .unwrap();
    ///
    /// // Calling this function on the first div tag (#a) will return a slice containing 3 elements:
    /// // - whitespaces around (before and after) div#b
    /// // - div#b itself
    /// // It does **not** contain the inner span tags
    /// assert_eq!(a.children().top().len(), 3);
    /// ```
    #[inline]
    pub fn top(&self) -> &RawChildren {
        &self.0._children
    }

    /// Returns the starting boundary of the children of this tag.
    #[inline]
    pub fn start(&self) -> Option<InnerNodeHandle> {
        self.0._children.get(0).map(NodeHandle::get_inner)
    }

    /// Returns the ending boundary of the children of this tag.
    pub fn end(&self, parser: &Parser<'a>) -> Option<InnerNodeHandle> {
        find_last_node_handle(self.0, parser).map(|h| h.get_inner())
    }

    /// Returns the (start, end) boundaries of the children of this tag.
    #[inline]
    pub fn boundaries(&self, parser: &Parser<'a>) -> Option<(InnerNodeHandle, InnerNodeHandle)> {
        self.start().zip(self.end(parser))
    }

    /// Returns a slice containing all of the children of this [`HTMLTag`],
    /// including all subnodes of the children.
    ///
    /// The difference between `top()` and `all()` is the same as `VDom::children()` and `VDom::nodes()`
    ///
    /// # Example
    /// ```
    /// let dom = tl::parse(r#"
    ///     <div id="a"><div id="b"><span>Hello</span><span>World</span><span>!</span></div></div>
    /// "#, Default::default()).unwrap();
    ///
    /// let a = dom.get_element_by_id("a")
    ///     .unwrap()
    ///     .get(dom.parser())
    ///     .unwrap()
    ///     .as_tag()
    ///     .unwrap();
    ///
    /// // Calling this function on the first div tag (#a) will return a slice containing all of the subnodes:
    /// // - div#b
    /// // - span
    /// // - Hello
    /// // - span
    /// // - World
    /// // - span
    /// // - !
    /// assert_eq!(a.children().all(dom.parser()).len(), 7);
    /// ```
    pub fn all(&self, parser: &'b Parser<'a>) -> &'b [Node<'a>] {
        self.boundaries(parser)
            .map(|(start, end)| &parser.tags[start as usize..=end as usize])
            .unwrap_or(&[])
    }
}

/// A thin mutable wrapper around the children of [`HTMLTag`]
#[derive(Debug)]
pub struct ChildrenMut<'a, 'b>(&'b mut HTMLTag<'a>);

impl<'a, 'b> ChildrenMut<'a, 'b> {
    /// Returns the topmost, direct children of this tag as a mutable slice.
    ///
    /// See [`Children::top`] for more details and examples.
    #[inline]
    pub fn top_mut(&mut self) -> &mut RawChildren {
        &mut self.0._children
    }
}

/// Attempts to find the very last node handle that is contained in the given tag
fn find_last_node_handle<'a>(tag: &HTMLTag<'a>, parser: &Parser<'a>) -> Option<NodeHandle> {
    let last_handle = tag._children.as_slice().last().copied()?;

    let child = last_handle
        .get(parser)
        .expect("Failed to get child node, please open a bug report") // this shouldn't happen
        .as_tag();

    if let Some(child) = child {
        // Recursively call this function to get to the innermost node
        find_last_node_handle(child, parser).or(Some(last_handle))
    } else {
        Some(last_handle)
    }
}

/// An HTML Node
#[derive(Debug, Clone)]
pub enum Node<'a> {
    /// A regular HTML element/tag
    Tag(HTMLTag<'a>),
    /// Raw text (no particular HTML element)
    Raw(Bytes<'a>),
    /// Comment (<!-- -->)
    Comment(Bytes<'a>),
}

impl<'a> Node<'a> {
    /// Returns the inner text of this node
    pub fn inner_text<'s, 'p: 's>(&'s self, parser: &'p Parser<'a>) -> Cow<'s, str> {
        match self {
            Node::Comment(_) => Cow::Borrowed(""),
            Node::Raw(r) => r.as_utf8_str(),
            Node::Tag(t) => t.inner_text(parser),
        }
    }

    /// Returns the inner HTML of this node
    pub fn inner_html<'s>(&'s self) -> &'s Bytes<'a> {
        match self {
            Node::Comment(c) => c,
            Node::Raw(r) => r,
            Node::Tag(t) => t.inner_html(),
        }
    }

    /// Returns an iterator over subnodes ("children") of this HTML tag, if this is a tag
    pub fn children(&self) -> Option<Children<'a, '_>> {
        match self {
            Node::Tag(t) => Some(t.children()),
            _ => None,
        }
    }

    /// Calls the given closure with each tag as parameter
    ///
    /// The closure must return a boolean, indicating whether it should stop iterating
    /// Returning `true` will break the loop and return a handle to the node
    pub fn find_node<F>(&self, parser: &Parser<'a>, f: &mut F) -> Option<NodeHandle>
    where
        F: FnMut(&Node<'a>) -> bool,
    {
        if let Some(children) = self.children() {
            for &id in children.top().iter() {
                let node = id.get(parser).unwrap();

                if f(node) {
                    return Some(id);
                }

                let subnode = node.find_node(parser, f);
                if subnode.is_some() {
                    return subnode;
                }
            }
        }
        None
    }

    /// Tries to coerce this node into a `HTMLTag` variant
    pub fn as_tag(&self) -> Option<&HTMLTag<'a>> {
        match self {
            Self::Tag(tag) => Some(tag),
            _ => None,
        }
    }

    /// Tries to coerce this node into a `HTMLTag` variant
    pub fn as_tag_mut(&mut self) -> Option<&mut HTMLTag<'a>> {
        match self {
            Self::Tag(tag) => Some(tag),
            _ => None,
        }
    }

    /// Tries to coerce this node into a comment, returning the text
    pub fn as_comment(&self) -> Option<&Bytes<'a>> {
        match self {
            Self::Comment(c) => Some(c),
            _ => None,
        }
    }

    /// Tries to coerce this node into a comment, returning the text
    pub fn as_comment_mut(&mut self) -> Option<&mut Bytes<'a>> {
        match self {
            Self::Comment(c) => Some(c),
            _ => None,
        }
    }

    /// Tries to coerce this node into a raw text node, returning the text
    ///
    /// "Raw text nodes" are nodes that are not HTML tags, but just text
    pub fn as_raw(&self) -> Option<&Bytes<'a>> {
        match self {
            Self::Raw(r) => Some(r),
            _ => None,
        }
    }

    /// Tries to coerce this node into a mutable raw text node, returning the text
    ///
    /// "Raw text nodes" are nodes that are not HTML tags, but just text
    pub fn as_raw_mut(&mut self) -> Option<&mut Bytes<'a>> {
        match self {
            Self::Raw(r) => Some(r),
            _ => None,
        }
    }
}
