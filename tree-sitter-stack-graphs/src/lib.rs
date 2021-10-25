// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2021, stack-graphs authors.
// Licensed under either of Apache License, Version 2.0, or MIT license, at your option.
// Please see the LICENSE-APACHE or LICENSE-MIT files in this distribution for license details.
// ------------------------------------------------------------------------------------------------

use lsp_positions::Span;
use lsp_positions::SpanCalculator;
use stack_graphs::arena::Handle;
use stack_graphs::arena::SupplementalArena;
use stack_graphs::graph::File;
use stack_graphs::graph::Node;
use stack_graphs::graph::NodeID;
use stack_graphs::graph::StackGraph;
use thiserror::Error;
use tree_sitter_graph::graph::Graph;
use tree_sitter_graph::graph::GraphNode;
use tree_sitter_graph::graph::GraphNodeRef;

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
}

pub trait LoadGraph {
    fn load_into_graph(
        &self,
        source: &str,
        stack_graph: &mut StackGraph,
        spans: &mut SupplementalArena<Node, Span>,
        file: Handle<File>,
    ) -> Result<(), LoadError>;
}

impl LoadGraph for Graph<'_> {
    fn load_into_graph(
        &self,
        source: &str,
        stack_graph: &mut StackGraph,
        spans: &mut SupplementalArena<Node, Span>,
        file: Handle<File>,
    ) -> Result<(), LoadError> {
        let mut span_calculator = SpanCalculator::new(source);
        let mut sg_nodes = Vec::with_capacity(self.node_count());
        for (index, node_ref) in self.iter_nodes().enumerate() {
            let node = &self[node_ref];
            let handle = match get_node_type(node, node_ref)? {
                NodeType::Definition => load_definition(stack_graph, file, index, node, node_ref)?,
                NodeType::DropScopes => load_drop_scopes(stack_graph, file, index),
                NodeType::ExportedScope => load_exported_scope(stack_graph, file, index),
                NodeType::InternalScope => load_internal_scope(stack_graph, file, index),
                NodeType::JumpTo => load_jump_to_scope(stack_graph),
                NodeType::PopSymbol => load_pop_symbol(stack_graph, file, index, node, node_ref)?,
                NodeType::PushSymbol => load_push_symbol(stack_graph, file, index, node, node_ref)?,
                NodeType::Reference => load_reference(stack_graph, file, index, node, node_ref)?,
                NodeType::Root => load_root(stack_graph),
            };
            load_span(spans, &mut span_calculator, self, node, handle)?;
            sg_nodes.push(handle);
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

fn load_definition(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
    node: &GraphNode,
    node_ref: GraphNodeRef,
) -> Result<Handle<Node>, LoadError> {
    let symbol = match node.attributes.get("symbol") {
        Some(symbol) => symbol.as_str()?,
        None => return Err(LoadError::MissingSymbol(node_ref)),
    };
    let symbol = stack_graph.add_symbol(symbol);
    let id = NodeID::new_in_file(file, index as u32);
    Ok(stack_graph.add_pop_symbol_node(id, symbol, true).unwrap())
}

fn load_drop_scopes(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
) -> Handle<Node> {
    let id = NodeID::new_in_file(file, index as u32);
    stack_graph.add_drop_scopes_node(id).unwrap()
}

fn load_exported_scope(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
) -> Handle<Node> {
    let id = NodeID::new_in_file(file, index as u32);
    stack_graph.add_exported_scope_node(id).unwrap()
}

fn load_internal_scope(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
) -> Handle<Node> {
    let id = NodeID::new_in_file(file, index as u32);
    stack_graph.add_internal_scope_node(id).unwrap()
}

fn load_jump_to_scope(stack_graph: &mut StackGraph) -> Handle<Node> {
    stack_graph.jump_to_node()
}

fn load_pop_symbol(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
    node: &GraphNode,
    node_ref: GraphNodeRef,
) -> Result<Handle<Node>, LoadError> {
    let symbol = match node.attributes.get("symbol") {
        Some(symbol) => symbol.as_str()?,
        None => return Err(LoadError::MissingSymbol(node_ref)),
    };
    let symbol = stack_graph.add_symbol(symbol);
    let id = NodeID::new_in_file(file, index as u32);
    if let Some(scoped) = node.attributes.get("scoped") {
        if scoped.as_boolean()? {
            return Ok(stack_graph
                .add_pop_scoped_symbol_node(id, symbol, false)
                .unwrap());
        }
    }
    Ok(stack_graph.add_pop_symbol_node(id, symbol, false).unwrap())
}

fn load_push_symbol(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
    node: &GraphNode,
    node_ref: GraphNodeRef,
) -> Result<Handle<Node>, LoadError> {
    let symbol = match node.attributes.get("symbol") {
        Some(symbol) => symbol.as_str()?,
        None => return Err(LoadError::MissingSymbol(node_ref)),
    };
    let symbol = stack_graph.add_symbol(symbol);
    let id = NodeID::new_in_file(file, index as u32);
    if let Some(scope) = node.attributes.get("scope") {
        let scope = scope.as_graph_node()?;
        let scope = NodeID::new_in_file(file, scope.index() as u32);
        return Ok(stack_graph
            .add_push_scoped_symbol_node(id, symbol, scope, false)
            .unwrap());
    }
    Ok(stack_graph.add_push_symbol_node(id, symbol, false).unwrap())
}

fn load_reference(
    stack_graph: &mut StackGraph,
    file: Handle<File>,
    index: usize,
    node: &GraphNode,
    node_ref: GraphNodeRef,
) -> Result<Handle<Node>, LoadError> {
    let symbol = match node.attributes.get("symbol") {
        Some(symbol) => symbol.as_str()?,
        None => return Err(LoadError::MissingSymbol(node_ref)),
    };
    let symbol = stack_graph.add_symbol(symbol);
    let id = NodeID::new_in_file(file, index as u32);
    Ok(stack_graph.add_push_symbol_node(id, symbol, true).unwrap())
}

fn load_root(stack_graph: &mut StackGraph) -> Handle<Node> {
    stack_graph.root_node()
}

fn load_span(
    spans: &mut SupplementalArena<Node, Span>,
    span_calculator: &mut SpanCalculator,
    graph: &Graph,
    node: &GraphNode,
    node_handle: Handle<Node>,
) -> Result<(), LoadError> {
    let source_node = match node.attributes.get("source_node") {
        Some(source_node) => source_node.as_syntax_node(graph)?,
        None => return Ok(()),
    };
    spans[node_handle] = span_calculator.for_node(source_node);
    Ok(())
}
