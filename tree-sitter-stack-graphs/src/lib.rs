// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2021, stack-graphs authors.
// Licensed under either of Apache License, Version 2.0, or MIT license, at your option.
// Please see the LICENSE-APACHE or LICENSE-MIT files in this distribution for license details.
// ------------------------------------------------------------------------------------------------

use lsp_positions::SpanCalculator;
use stack_graphs::arena::Handle;
use stack_graphs::graph::File;
use stack_graphs::graph::Node;
use stack_graphs::graph::NodeID;
use stack_graphs::graph::StackGraph;
use thiserror::Error;
use tree_sitter::Parser;
use tree_sitter_graph::functions::Functions;
use tree_sitter_graph::graph::Graph;
use tree_sitter_graph::graph::GraphNode;
use tree_sitter_graph::graph::GraphNodeRef;
use tree_sitter_graph::Variables;

pub struct StackGraphLanguage {
    parser: Parser,
    tsg: tree_sitter_graph::ast::File,
    functions: Functions,
    globals: Variables,
}

impl StackGraphLanguage {
    pub fn from_language(language: tree_sitter::Language) -> StackGraphLanguage {
        let mut parser = Parser::new();
        parser.set_language(language).unwrap();
        let tsg = tree_sitter_graph::ast::File::new(language);
        // TODO: Load in TSG file from grammar repo
        let functions = Functions::stdlib();
        let globals = Variables::new();
        StackGraphLanguage {
            parser,
            tsg,
            functions,
            globals,
        }
    }

    pub fn load_stack_graph(
        &mut self,
        stack_graph: &mut StackGraph,
        file: Handle<File>,
        source: &str,
    ) -> Result<(), LoadError> {
        let tree = self
            .parser
            .parse(source, None)
            .ok_or(LoadError::ParseError)?;
        let graph = self
            .tsg
            .execute(&tree, source, &mut self.functions, &mut self.globals)?;
        let mut loader = StackGraphLoader {
            stack_graph,
            file,
            graph: &graph,
            span_calculator: SpanCalculator::new(source),
            nodes: Vec::new(),
        };
        loader.load()
    }
}

/// An error that can occur while loading a stack graph from a TSG file
#[derive(Debug, Error)]
pub enum LoadError {
    #[error("Missing ‘type’ attribute on graph node")]
    MissingNodeType(GraphNodeRef),
    #[error("Missing ‘symbol’ attribute on graph node")]
    MissingSymbol(GraphNodeRef),
    #[error("Unknown node type {0}")]
    UnknownNodeType(String),
    #[error(transparent)]
    ExecutionError(#[from] tree_sitter_graph::ExecutionError),
    #[error("Error parsing source")]
    ParseError,
}

struct StackGraphLoader<'a> {
    stack_graph: &'a mut StackGraph,
    file: Handle<File>,
    graph: &'a Graph<'a>,
    span_calculator: SpanCalculator<'a>,
    nodes: Vec<Handle<Node>>,
}

impl<'a> StackGraphLoader<'a> {
    fn load(&mut self) -> Result<(), LoadError> {
        self.nodes.reserve(self.graph.node_count());
        for (index, node_ref) in self.graph.iter_nodes().enumerate() {
            let node = &self.graph[node_ref];
            let handle = match get_node_type(node, node_ref)? {
                NodeType::Definition => self.load_definition(index, node, node_ref)?,
                NodeType::DropScopes => self.load_drop_scopes(index),
                NodeType::ExportedScope => self.load_exported_scope(index),
                NodeType::InternalScope => self.load_internal_scope(index),
                NodeType::JumpTo => self.load_jump_to_scope(),
                NodeType::PopSymbol => self.load_pop_symbol(index, node, node_ref)?,
                NodeType::PushSymbol => self.load_push_symbol(index, node, node_ref)?,
                NodeType::Reference => self.load_reference(index, node, node_ref)?,
                NodeType::Root => self.load_root(),
            };
            self.load_span(node, handle)?;
            self.nodes.push(handle);
        }
        Ok(())
    }
}

enum NodeType {
    Definition,
    DropScopes,
    ExportedScope,
    InternalScope,
    JumpTo,
    PopSymbol,
    PushSymbol,
    Reference,
    Root,
}

fn get_node_type(node: &GraphNode, node_ref: GraphNodeRef) -> Result<NodeType, LoadError> {
    let node_type = match node.attributes.get("type") {
        Some(node_type) => node_type.as_str()?,
        None => return Err(LoadError::MissingNodeType(node_ref)),
    };
    if node_type == "definition" {
        return Ok(NodeType::Definition);
    } else if node_type == "drop" {
        return Ok(NodeType::DropScopes);
    } else if node_type == "exported" || node_type == "endpoint" {
        return Ok(NodeType::ExportedScope);
    } else if node_type == "internal" {
        return Ok(NodeType::InternalScope);
    } else if node_type == "jump" {
        return Ok(NodeType::JumpTo);
    } else if node_type == "pop" {
        return Ok(NodeType::PopSymbol);
    } else if node_type == "push" {
        return Ok(NodeType::PushSymbol);
    } else if node_type == "reference" {
        return Ok(NodeType::Reference);
    } else if node_type == "root" {
        return Ok(NodeType::Root);
    } else {
        return Err(LoadError::UnknownNodeType(format!("{:?}", node_type)));
    }
}

impl<'a> StackGraphLoader<'a> {
    fn load_definition(
        &mut self,
        index: usize,
        node: &GraphNode,
        node_ref: GraphNodeRef,
    ) -> Result<Handle<Node>, LoadError> {
        let symbol = match node.attributes.get("symbol") {
            Some(symbol) => symbol.as_str()?,
            None => return Err(LoadError::MissingSymbol(node_ref)),
        };
        let symbol = self.stack_graph.add_symbol(symbol);
        let id = NodeID::new_in_file(self.file, index as u32);
        Ok(self
            .stack_graph
            .add_pop_symbol_node(id, symbol, true)
            .unwrap())
    }

    fn load_drop_scopes(&mut self, index: usize) -> Handle<Node> {
        let id = NodeID::new_in_file(self.file, index as u32);
        self.stack_graph.add_drop_scopes_node(id).unwrap()
    }

    fn load_exported_scope(&mut self, index: usize) -> Handle<Node> {
        let id = NodeID::new_in_file(self.file, index as u32);
        self.stack_graph.add_exported_scope_node(id).unwrap()
    }

    fn load_internal_scope(&mut self, index: usize) -> Handle<Node> {
        let id = NodeID::new_in_file(self.file, index as u32);
        self.stack_graph.add_internal_scope_node(id).unwrap()
    }

    fn load_jump_to_scope(&mut self) -> Handle<Node> {
        self.stack_graph.jump_to_node()
    }

    fn load_pop_symbol(
        &mut self,
        index: usize,
        node: &GraphNode,
        node_ref: GraphNodeRef,
    ) -> Result<Handle<Node>, LoadError> {
        let symbol = match node.attributes.get("symbol") {
            Some(symbol) => symbol.as_str()?,
            None => return Err(LoadError::MissingSymbol(node_ref)),
        };
        let symbol = self.stack_graph.add_symbol(symbol);
        let id = NodeID::new_in_file(self.file, index as u32);
        if let Some(scoped) = node.attributes.get("scoped") {
            if scoped.as_boolean()? {
                return Ok(self
                    .stack_graph
                    .add_pop_scoped_symbol_node(id, symbol, false)
                    .unwrap());
            }
        }
        Ok(self
            .stack_graph
            .add_pop_symbol_node(id, symbol, false)
            .unwrap())
    }

    fn load_push_symbol(
        &mut self,
        index: usize,
        node: &GraphNode,
        node_ref: GraphNodeRef,
    ) -> Result<Handle<Node>, LoadError> {
        let symbol = match node.attributes.get("symbol") {
            Some(symbol) => symbol.as_str()?,
            None => return Err(LoadError::MissingSymbol(node_ref)),
        };
        let symbol = self.stack_graph.add_symbol(symbol);
        let id = NodeID::new_in_file(self.file, index as u32);
        if let Some(scope) = node.attributes.get("scope") {
            let scope = scope.as_graph_node()?;
            let scope = NodeID::new_in_file(self.file, scope.index() as u32);
            return Ok(self
                .stack_graph
                .add_push_scoped_symbol_node(id, symbol, scope, false)
                .unwrap());
        }
        Ok(self
            .stack_graph
            .add_push_symbol_node(id, symbol, false)
            .unwrap())
    }

    fn load_reference(
        &mut self,
        index: usize,
        node: &GraphNode,
        node_ref: GraphNodeRef,
    ) -> Result<Handle<Node>, LoadError> {
        let symbol = match node.attributes.get("symbol") {
            Some(symbol) => symbol.as_str()?,
            None => return Err(LoadError::MissingSymbol(node_ref)),
        };
        let symbol = self.stack_graph.add_symbol(symbol);
        let id = NodeID::new_in_file(self.file, index as u32);
        Ok(self
            .stack_graph
            .add_push_symbol_node(id, symbol, true)
            .unwrap())
    }

    fn load_root(&mut self) -> Handle<Node> {
        self.stack_graph.root_node()
    }

    fn load_span(&mut self, node: &GraphNode, node_handle: Handle<Node>) -> Result<(), LoadError> {
        let source_node = match node.attributes.get("source_node") {
            Some(source_node) => source_node.as_syntax_node(self.graph)?,
            None => return Ok(()),
        };
        *self.stack_graph.span_mut(node_handle) = self.span_calculator.for_node(source_node);
        Ok(())
    }
}
