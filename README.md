# xorlinkedlist

A linked list that allows bidirectional traversal while only using one
pointer per node. [How it works.](https://en.wikipedia.org/wiki/XOR_linked_list)

XOR Linked Lists have a few advantages over traditional linked lists. Besides the
obvious space savings that are achieved by only using one pointer per node, another
advantage is that reversing a linked list is an *O*(1) operation, as you only have to swap
the head and tail pointers. That's why the [`XORLinkedList`] provides a [`reverse`] method
while the standard library [`LinkedList`] doesn't.

[`LinkedList`]: std::collections::LinkedList
[`XORLinkedList`]: crate::XORLinkedList
[`reverse`]: crate::XORLinkedList::reverse
