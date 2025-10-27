// Project type detection and configuration
// Detects project type and infers entry points from tsconfig.json, package.json, etc.

import * as fs from "node:fs";
import * as path from "node:path";
import type { ProjectConfig, ProjectType } from "../types/architecture";

/**
 * Detect project type and generate configuration
 * Falls back to tsconfig.json when manifest.json is not available
 */
export class ProjectDetector {
	private projectRoot: string;

	constructor(projectRoot: string) {
		this.projectRoot = projectRoot;
	}

	/**
	 * Detect project type and return configuration
	 */
	detect(): ProjectConfig {
		// Check for Chrome extension manifest
		const manifestPath = path.join(this.projectRoot, "manifest.json");
		if (fs.existsSync(manifestPath)) {
			return this.detectChromeExtension(manifestPath);
		}

		// Check for PWA manifest
		const pwaManifestPath = path.join(
			this.projectRoot,
			"public",
			"manifest.json",
		);
		if (fs.existsSync(pwaManifestPath)) {
			return this.detectPWA(pwaManifestPath);
		}

		// Check for Electron
		const packageJsonPath = path.join(this.projectRoot, "package.json");
		if (fs.existsSync(packageJsonPath)) {
			const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, "utf-8"));

			if (
				packageJson.dependencies?.electron ||
				packageJson.devDependencies?.electron
			) {
				return this.detectElectron(packageJson);
			}

			// Check for WebSocket/server patterns
			if (
				packageJson.dependencies?.ws ||
				packageJson.dependencies?.["socket.io"] ||
				packageJson.dependencies?.elysia ||
				packageJson.dependencies?.express
			) {
				return this.detectWebSocketApp(packageJson);
			}
		}

		// Fallback: Generic TypeScript project
		return this.detectGenericProject();
	}

	/**
	 * Detect Chrome extension from manifest.json
	 */
	private detectChromeExtension(manifestPath: string): ProjectConfig {
		const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
		const entryPoints: Record<string, string> = {};

		// Background
		const background = manifest.background;
		if (background) {
			const file =
				background.service_worker || background.scripts?.[0] || background.page;
			if (file) {
				entryPoints.background = this.findSourceFile(file);
			}
		}

		// Content scripts
		const contentScripts = manifest.content_scripts;
		if (contentScripts && contentScripts.length > 0) {
			const firstScript = contentScripts[0].js?.[0];
			if (firstScript) {
				entryPoints.content = this.findSourceFile(firstScript);
			}
		}

		// Popup
		const popup =
			manifest.action?.default_popup || manifest.browser_action?.default_popup;
		if (popup) {
			const jsFile = this.findAssociatedJS(path.join(this.projectRoot, popup));
			if (jsFile) entryPoints.popup = jsFile;
		}

		// Options
		const options = manifest.options_ui?.page || manifest.options_page;
		if (options) {
			const jsFile = this.findAssociatedJS(
				path.join(this.projectRoot, options),
			);
			if (jsFile) entryPoints.options = jsFile;
		}

		return {
			type: "chrome-extension",
			entryPoints,
			metadata: {
				name: manifest.name,
				version: manifest.version,
				description: manifest.description,
			},
		};
	}

	/**
	 * Detect PWA from manifest.json
	 */
	private detectPWA(manifestPath: string): ProjectConfig {
		const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf-8"));
		const entryPoints: Record<string, string> = {};

		// Look for service worker
		const swCandidates = [
			"src/service-worker.ts",
			"src/sw.ts",
			"public/service-worker.js",
			"public/sw.js",
		];

		for (const candidate of swCandidates) {
			const fullPath = path.join(this.projectRoot, candidate);
			if (fs.existsSync(fullPath)) {
				entryPoints.worker = fullPath;
				break;
			}
		}

		// Look for main client entry
		const clientCandidates = [
			"src/main.ts",
			"src/index.ts",
			"src/app.ts",
			"src/main.tsx",
			"src/index.tsx",
		];

		for (const candidate of clientCandidates) {
			const fullPath = path.join(this.projectRoot, candidate);
			if (fs.existsSync(fullPath)) {
				entryPoints.client = fullPath;
				break;
			}
		}

		return {
			type: "pwa",
			entryPoints,
			contextMapping: {
				worker: "Service Worker",
				client: "Client App",
			},
			metadata: {
				name: manifest.name || manifest.short_name,
				version: "1.0.0",
				description: manifest.description,
			},
		};
	}

	/**
	 * Detect Electron app
	 */
	private detectElectron(packageJson: any): ProjectConfig {
		const entryPoints: Record<string, string> = {};

		// Main process
		const mainCandidates = [
			packageJson.main,
			"src/main/index.ts",
			"src/electron/main.ts",
			"electron/main.ts",
			"main.ts",
		].filter(Boolean);

		for (const candidate of mainCandidates) {
			const fullPath = path.join(this.projectRoot, candidate!);
			if (
				fs.existsSync(fullPath) ||
				fs.existsSync(fullPath.replace(/\.js$/, ".ts"))
			) {
				entryPoints.main = fs.existsSync(fullPath)
					? fullPath
					: fullPath.replace(/\.js$/, ".ts");
				break;
			}
		}

		// Renderer process
		const rendererCandidates = [
			"src/renderer/index.tsx",
			"src/renderer/index.ts",
			"src/index.tsx",
			"src/index.ts",
		];

		for (const candidate of rendererCandidates) {
			const fullPath = path.join(this.projectRoot, candidate);
			if (fs.existsSync(fullPath)) {
				entryPoints.renderer = fullPath;
				break;
			}
		}

		return {
			type: "electron",
			entryPoints,
			contextMapping: {
				main: "Main Process",
				renderer: "Renderer Process",
			},
			metadata: {
				name: packageJson.name,
				version: packageJson.version,
				description: packageJson.description,
			},
		};
	}

	/**
	 * Detect WebSocket/server app
	 */
	private detectWebSocketApp(packageJson: any): ProjectConfig {
		const entryPoints: Record<string, string> = {};

		// Server entry point
		const serverCandidates = [
			"src/server.ts",
			"src/index.ts",
			"src/main.ts",
			"src/app.ts",
			"server.ts",
			"index.ts",
		];

		for (const candidate of serverCandidates) {
			const fullPath = path.join(this.projectRoot, candidate);
			if (fs.existsSync(fullPath)) {
				entryPoints.server = fullPath;
				break;
			}
		}

		// Client entry point (if exists)
		const clientCandidates = [
			"src/client/index.ts",
			"src/client.ts",
			"client/index.ts",
		];

		for (const candidate of clientCandidates) {
			const fullPath = path.join(this.projectRoot, candidate);
			if (fs.existsSync(fullPath)) {
				entryPoints.client = fullPath;
				break;
			}
		}

		return {
			type: "websocket-app",
			entryPoints,
			contextMapping: {
				server: "Server",
				client: "Client",
			},
			metadata: {
				name: packageJson.name,
				version: packageJson.version,
				description: packageJson.description,
			},
		};
	}

	/**
	 * Fallback: Generic TypeScript project
	 * Uses tsconfig.json to find entry points
	 */
	private detectGenericProject(): ProjectConfig {
		const entryPoints: Record<string, string> = {};

		// Try to find tsconfig.json
		const tsConfigPath = path.join(this.projectRoot, "tsconfig.json");
		if (fs.existsSync(tsConfigPath)) {
			try {
				const tsConfig = JSON.parse(fs.readFileSync(tsConfigPath, "utf-8"));

				// Check for entry points in various locations
				if (tsConfig.files && Array.isArray(tsConfig.files)) {
					tsConfig.files.forEach((file: string, idx: number) => {
						const fullPath = path.join(this.projectRoot, file);
						if (fs.existsSync(fullPath)) {
							entryPoints[`module${idx + 1}`] = fullPath;
						}
					});
				}
			} catch (error) {
				console.warn(`Failed to parse tsconfig.json: ${error}`);
			}
		}

		// If no entry points found, scan src directory
		if (Object.keys(entryPoints).length === 0) {
			const commonEntries = [
				"src/index.ts",
				"src/main.ts",
				"src/app.ts",
				"index.ts",
				"main.ts",
			];

			for (const candidate of commonEntries) {
				const fullPath = path.join(this.projectRoot, candidate);
				if (fs.existsSync(fullPath)) {
					entryPoints.main = fullPath;
					break;
				}
			}
		}

		// Get metadata from package.json
		const packageJsonPath = path.join(this.projectRoot, "package.json");
		let metadata: ProjectConfig["metadata"] = { name: "Unknown Project" };

		if (fs.existsSync(packageJsonPath)) {
			try {
				const packageJson = JSON.parse(
					fs.readFileSync(packageJsonPath, "utf-8"),
				);
				metadata = {
					name: packageJson.name,
					version: packageJson.version,
					description: packageJson.description,
				};
			} catch (error) {
				console.warn(`Failed to parse package.json: ${error}`);
			}
		}

		return {
			type: "generic",
			entryPoints,
			metadata,
		};
	}

	/**
	 * Find source file from manifest reference
	 */
	private findSourceFile(manifestPath: string): string {
		const candidates = [
			path.join(this.projectRoot, manifestPath),
			path.join(this.projectRoot, manifestPath.replace(/\.js$/, ".ts")),
			path.join(this.projectRoot, "src", manifestPath),
			path.join(this.projectRoot, "src", manifestPath.replace(/\.js$/, ".ts")),
			path.join(this.projectRoot, "src", manifestPath.replace(/\.js$/, ".tsx")),
		];

		for (const candidate of candidates) {
			if (fs.existsSync(candidate)) {
				return candidate;
			}
		}

		return path.join(this.projectRoot, manifestPath);
	}

	/**
	 * Find associated JavaScript/TypeScript file for an HTML file
	 */
	private findAssociatedJS(htmlPath: string): string | null {
		if (!fs.existsSync(htmlPath)) {
			return null;
		}

		// Read HTML and look for script tags
		const html = fs.readFileSync(htmlPath, "utf-8");
		const scriptMatch = html.match(/<script[^>]+src=["']([^"']+)["']/i);

		if (scriptMatch && scriptMatch[1]) {
			const scriptPath = scriptMatch[1];
			const fullPath = path.resolve(path.dirname(htmlPath), scriptPath);

			if (fs.existsSync(fullPath)) return fullPath;
			if (fs.existsSync(fullPath.replace(/\.js$/, ".ts"))) {
				return fullPath.replace(/\.js$/, ".ts");
			}
			if (fs.existsSync(fullPath.replace(/\.js$/, ".tsx"))) {
				return fullPath.replace(/\.js$/, ".tsx");
			}
		}

		// Fallback: convention-based files
		const baseName = path.basename(htmlPath, ".html");
		const dir = path.dirname(htmlPath);

		const candidates = [
			path.join(dir, `${baseName}.ts`),
			path.join(dir, `${baseName}.tsx`),
			path.join(dir, `${baseName}.js`),
			path.join(dir, "index.ts"),
			path.join(dir, "index.tsx"),
		];

		for (const candidate of candidates) {
			if (fs.existsSync(candidate)) {
				return candidate;
			}
		}

		return null;
	}
}

/**
 * Detect project configuration from project root
 */
export function detectProjectConfig(projectRoot: string): ProjectConfig {
	const detector = new ProjectDetector(projectRoot);
	return detector.detect();
}
