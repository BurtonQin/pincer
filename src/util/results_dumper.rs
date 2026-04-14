use log::*;
use std::collections::HashSet;
use std::fs::{File, create_dir_all};
use std::io::Write;

use crate::mir::body_ext::BodyExt;
use crate::analysis_context::AnalysisContext;

pub fn dump_call_graph(acx: &AnalysisContext) {
    if !acx.analysis_options.dump_call_graph {
        return;
    }
    info!("Dumping call graph...");
    if let Some(call_graph) = &acx.call_graph {
        let cg_path = acx.analysis_options.call_graph_output_path();
        create_dir_all(acx.analysis_options.output_dir.clone()).expect("Failed to create the output directory");
        call_graph.to_dot(&cg_path);
    }
}

pub fn dump_mir(acx: &AnalysisContext) {
    if !acx.analysis_options.dump_mir {
        return;
    }
    info!("Dumping functions' mir...");
    let mir_path = acx.analysis_options.mir_output_path();
    create_dir_all(acx.analysis_options.output_dir.clone()).expect("Failed to create the output directory");
    let mut mir_writer = File::create(mir_path).expect("Unable to create file");
    let mut visited_func = HashSet::new();
    if let Some(call_graph) = &acx.call_graph {
        for func in call_graph.reachable_funcs_iter() {
            let def_id = func.def_id;
            if visited_func.contains(&def_id) {
                continue;
            }
            visited_func.insert(def_id);
            mir_writer
                .write_all(format!("{:?}\n", def_id).as_bytes())
                .expect("Unable to write data");
            mir_writer
                .write_all(format!("{:?}\n", acx.tcx.def_path_str(def_id)).as_bytes())
                .expect("Unable to write data");
            if !acx.tcx.is_mir_available(def_id) {
                mir_writer.write_all(("Mir is unavailable\n").as_bytes()).expect("Unable to write data");
            } else {
                let body = acx.tcx.optimized_mir(def_id);
                mir_writer.write_all(body.to_string(acx.tcx).unwrap().as_bytes()).expect("Unable to write data");
            }
            mir_writer.write_all("\n".as_bytes()).expect("Unable to write data");
        }
    }
}
