// Code generated by go tool dist; DO NOT EDIT.
// This is a bootstrap copy of /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/compile/internal/base/bootstrap_false.go

//line /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/compile/internal/base/bootstrap_false.go:1
// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !compiler_bootstrap
// +build !compiler_bootstrap

package base

// CompilerBootstrap reports whether the current compiler binary was
// built with -tags=compiler_bootstrap.
const CompilerBootstrap = false
