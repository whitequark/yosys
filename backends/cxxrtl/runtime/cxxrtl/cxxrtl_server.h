/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  Catherine <whitequark@whitequark.org>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#ifndef CXXRTL_SERVER_H
#define CXXRTL_SERVER_H

#if !defined(WIN32)

#include <unistd.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>

#else

#define WIN32_LEAN_AND_MEAN
#include <fcntl.h>
#include <winsock2.h>
#include <ws2ipdef.h>
#include <in6addr.h>

#endif

#include <cinttypes>
#include <cstdio>
#include <string>
#include <unordered_set>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <nlohmann/json.hpp>

#include <cxxrtl/cxxrtl.h>
#include <cxxrtl/cxxrtl_replay.h>

namespace cxxrtl {

// Server<>debugger link, with several transport mechanisms available.
//
// The server<>debugger link abstracts away _how_ the packets are shuttled between the server and the debugger, and
// leaves the server to send and receive whole packets.

class basic_link {
protected:
	std::string recv_buf;
	std::string send_buf;

public:
	basic_link() = default;
	basic_link(basic_link &&) = default;
	basic_link(const basic_link &) = delete;
	basic_link &operator=(const basic_link &) = delete;

	// Retrieve a packet from the receive buffer.
	//
	// This method does not perform I/O and does not have error conditions.
	std::string recv() {
		size_t pos = recv_buf.find('\0');
		if (pos == std::string::npos)
			return "";
		std::string packet = recv_buf.substr(0, pos);
		recv_buf.erase(0, pos + 1);
		return packet;
	}

	// Place a packet into the transmit buffer.
	//
	// This method does not perform I/O and does not have error conditions.
	void send(const std::string &packet) {
		send_buf += packet;
		send_buf += '\0';
	}
};

class stdio_link : public basic_link {
public:
	std::string uri() const {
		return "cxxrtl+stdio://";
	}

	// Perform I/O. Returns `true` on success (timeout expiring is considered a success).
	bool poll(uint32_t timeout_ms) {
		// Empty send buffer.
		if (feof(stdout))
			return false;
		fwrite(&send_buf[0], 1, send_buf.size(), stdout);
		fflush(stdout);
		send_buf.erase();
		if (timeout_ms != 0) {
			// Wait for data to be received.
	#if !defined(WIN32)
			struct timeval tv = {};
			tv.tv_usec = timeout_ms * 1000;
			fd_set read_fds;
			FD_ZERO(&read_fds);
			FD_SET(STDIN_FILENO, &read_fds);
			if (select(STDIN_FILENO + 1, &read_fds, nullptr, nullptr, &tv) == 0)
				return true;
	#else
			if (WaitForSingleObject(GetStdHandle(STD_INPUT_HANDLE), timeout_ms) == WAIT_TIMEOUT)
				return true;
	#endif
		}
		// Fill receive buffer.
		if (feof(stdin))
			return false;
		std::string buffer(1024, '\0');
		int length = fread(&buffer[0], 1, buffer.size(), stdin);
		recv_buf.append(buffer.begin(), buffer.begin() + length);
		// Done.
		return true;
	}

	const char *poll_error() {
		return strerror(errno);
	}
};

class tcp_link : public basic_link {
	uint16_t listen_port = 0;
	int listenfd = -1;
	int connectfd = -1;

	void close() {
		recv_buf.erase();
		send_buf.erase();
		if (connectfd != -1)
			::close(connectfd);
		connectfd = -1;
	}

	void closeall() {
		close();
		if (listenfd != -1)
			::close(listenfd);
		listenfd = -1;
	}

public:
	tcp_link(uint16_t listen_port = 6618) : listen_port(listen_port) {
#if defined(WIN32)
		WSADATA wsaData;
		int wsaStartupResult = WSAStartup(MAKEWORD(2, 2), &wsaData);
		assert (wsaStartupResult == 0);
#endif
	}

	tcp_link(tcp_link &&moved) : basic_link(std::move(moved)), listen_port(moved.listen_port), listenfd(moved.listenfd), connectfd(moved.connectfd) {
		moved.listenfd = -1;
		moved.connectfd = -1;
#if defined(WIN32)
		WSADATA wsaData;
		WSAStartup(MAKEWORD(2, 2), &wsaData); // increment WSA reference count, to match destructor
#endif
	}

	~tcp_link() {
		closeall();
#if defined(WIN32)
		WSACleanup();
#endif
	}

	std::string uri() const {
		// We listen on IPv6 only, but some OSes will auto-listen on IPv4 too.
		return "cxxrtl+tcp://localhost:" + std::to_string(listen_port);
	}

	// Perform I/O. Returns `true` on success (timeout expiring is considered a success). If this function returns
	// `false`, further information can be retrieved from `errno`.
	bool poll(uint32_t timeout_ms) {
		// If the link is neither connected nor listening, create a listening socket.
		if (listenfd == -1) {
			// Open a new TCP socket.
			if ((listenfd = socket(AF_INET6, SOCK_STREAM, IPPROTO_TCP)) == -1) {
#ifdef CXXRTL_SERVER_TRACE
				fprintf(stderr, "S: socket(AF_INET6, SOCK_STREAM, IPPROTO_TCP) failed\n");
#endif
				return false;
			}
			// Enable SO_REUSEADDR to be able to bind to the same port again shortly after restart.
			int sockopt = 1;
			if (setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, (const char*)&sockopt, sizeof(sockopt)) == -1) {
#ifdef CXXRTL_SERVER_TRACE
				fprintf(stderr, "S: setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, 1, ...) failed\n");
#endif
				closeall();
				return false;
			}
			// Bind to `localhost:<listen_port>`.
			sockaddr_in6 sa = {};
			sa.sin6_family = AF_INET6;
			sa.sin6_addr = /*IN6ADDR_LOOPBACK_INIT*/ { { { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1 } } };
			sa.sin6_port = htons(listen_port);
			if (bind(listenfd, (sockaddr *)&sa, sizeof(sa)) == -1) {
#ifdef CXXRTL_SERVER_TRACE
				fprintf(stderr, "S: bind(fd, {AF_INET6, htons(port), IP6ADDR_LOOPBACK_INIT}, ...) failed\n");
#endif
				closeall();
				return false;
			}
			// Listen on the socket.
			if (listen(listenfd, /*backlog=*/1) == -1) {
#ifdef CXXRTL_SERVER_TRACE
				fprintf(stderr, "S: listen(fd, 1) failed\n");
#endif
				closeall();
				return false;
			}
		}
		// If the link is listening and not connected, accept a new connection.
		if (connectfd == -1) {
			if ((connectfd = accept(listenfd, nullptr, nullptr)) == -1) {
#ifdef CXXRTL_SERVER_TRACE
				fprintf(stderr, "S: accept(fd, ...) failed\n");
#endif
				// Do not close. The next attempt may succeed.
				return false;
			}
		}
		// Empty send buffer. Disconnect on any error.
		if (::send(connectfd, &send_buf[0], send_buf.size(), 0) == -1) {
			close();
			return false;
		}
		send_buf.erase();
		if (timeout_ms != 0) {
			// Wait for data to be received.
			struct timeval tv = {};
			tv.tv_usec = timeout_ms * 1000;
			fd_set read_fds;
			FD_ZERO(&read_fds);
			FD_SET(connectfd, &read_fds);
			if (select(connectfd + 1, &read_fds, nullptr, nullptr, &tv) == 0)
				return true;
		}
		// Fill receive buffer. Disconnect on any error.
		std::string buffer(1024, '\0');
		int length = 0;
		if ((length = ::recv(connectfd, &buffer[0], buffer.size(), 0)) == -1) {
			close();
			return false;
		}
		recv_buf.append(buffer.begin(), buffer.begin() + length);
		// If length is 0, the connection was gracefully closed.
		if (length == 0)
			close();
		// Done.
		return true;
	}

	const char *poll_error() {
#if !defined(WIN32)
		return strerror(errno);
#else
		return strerror(WSAGetLastError());
#endif
	}
};

// State that is shared between the agent and the server.
//
// This state is used by the server to signal that the agent should pause or reset the simulation, and by the agent
// to report timeline advancement.

enum class simulation_status {
	// Simulation is initializing. No samples have been recorded yet.
	initializing = 0,
	// Simulation is running. Samples are being actively recorded.
	running = 1,
	// Simulation is paused. No samples will be recorded until the simulation is unpaused.
	paused = 2,
	// Simulation is finished. The stimulus has ended, and no further samples will be recorded.
	finished = 3,
};

enum class diagnostic_type: uint32_t {
	breakpoint = 1 << 0, // avoid name clash with `break`
	print      = 1 << 1,
	assertion  = 1 << 2, // avoid name clash with `assert`
	assumption = 1 << 3,
};

enum class pause_reason {
	// Paused because the current time advanced past `run_until_time`.
	time = 0,
	// Paused because one of the diagnostics listed in `run_until_diagnostics` has been emitted.
	diagnostic = 1,
};

struct agent_server_state {
	// Shared state may be set or read while holding `mutex`. Waiting is coordinated using `condvar`.
	std::mutex mutex;
	std::condition_variable condvar;
	// Current status of the simulation. Set by the agent, read by the server.
	simulation_status status = simulation_status::initializing;
	// Timestamp of the last sample in the recorder. Set by the agent, read by the server.
	time latest_time;
	// Timestamp of the next sample that will be recorded if the simulation can progress. Set by the agent, read by
	// the server, valid only in the paused state.
	time next_sample_time;
	// Timestamp at which the simulation should be paused. Set by the server, read by the agent.
	time run_until_time = cxxrtl::time::maximum();
	// Diagnostics at which the simulation should be paused. Set by the server, read by the agent.
	uint32_t run_until_diagnostics = 0;
	// Cause of the simulation being paused by the agent. Set by the agent, read by the server.
	pause_reason cause;
	// Whether the simulation should be unpaused. Set by the server, cleared by the agent. Used for synchronization
	// of the "Run Simulation" command.
	bool unpause = false;
};

// Debug server.
//
// The server performs operations on an instance of the CXXRTL module as requested by the debugger, which communicates
// with the server using JSON packets over an abstracted link. It also exchanges state with the agent that is embedded
// in the user defined stimulus code.

std::string base64_encode(const char *data, size_t size) {
	static constexpr char alphabet[65] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

	size_t index;
	std::string encoded;
	for (index = 0; index + 3 <= size; index += 3) {
		uint32_t chunk = (data[index + 0] << 16) + (data[index + 1] << 8) + (data[index + 2] << 0);
		encoded.push_back(alphabet[(chunk >> 18) & 0x3f]);
		encoded.push_back(alphabet[(chunk >> 12) & 0x3f]);
		encoded.push_back(alphabet[(chunk >>  6) & 0x3f]);
		encoded.push_back(alphabet[(chunk >>  0) & 0x3f]);
	}
	if (index + 2 == size) {
		uint32_t chunk = (data[index + 0] << 16) + (data[index + 1] << 8);
		encoded.push_back(alphabet[(chunk >> 18) & 0x3f]);
		encoded.push_back(alphabet[(chunk >> 12) & 0x3f]);
		encoded.push_back(alphabet[(chunk >>  6) & 0x3f]);
		encoded.push_back('=');
	}
	if (index + 1 == size) {
		uint32_t chunk = (data[index + 0] << 16);
		encoded.push_back(alphabet[(chunk >> 18) & 0x3f]);
		encoded.push_back(alphabet[(chunk >> 12) & 0x3f]);
		encoded.push_back('=');
		encoded.push_back('=');
	}
	return encoded;
}

template<class LinkT, class ModuleT>
class server {
	using json = nlohmann::ordered_json;

	struct variable {
		size_t width;
		size_t chunks;
		chunk_t *data;
		size_t first_index;
		size_t last_index;
	};

	struct reference {
		std::vector<variable> variables;
		std::unordered_set<debug_outline*> outlines;
	};

	// Agent state.
	agent_server_state &shared_state;

	// Link state.
	LinkT link;
	bool got_greeting = false;
	bool emit_simulation_paused = false;
	bool emit_simulation_finished = false;

	// Simulation state.
	ModuleT toplevel;
	debug_items debug_items;
	debug_scopes debug_scopes;
	player player;

	// Protocol state.
	std::map<std::string, reference> references;

	// Command implementations.

	std::map<std::string, const debug_scope*> perform_list_scopes(bool all, const std::string &scope) {
		std::map<std::string, const debug_scope*> scopes = {};
		std::string current_scope = " invalid"; // cannot appear as a scope name
		for (auto &item : debug_items.table) {
			std::string item_scope = "";
			size_t pos = item.first.rfind(' ');
			if (pos != std::string::npos)
				item_scope = item.first.substr(0, pos);
			// All of the items in the same scope will be enumerated in a contiguous block, so to get a list of unique scopes
			// we only need to collapse runs of identical scopes into one.
			if (item_scope == current_scope)
				continue;
			if (all ||
					(scope.empty() && item_scope.find(' ') == std::string::npos) ||
					(!scope.empty() && item_scope.find(' ') != std::string::npos &&
					 item_scope.substr(0, item_scope.rfind(' ')) == scope))
				scopes[item_scope] = debug_scopes.contains(item_scope) ? &debug_scopes[item_scope] : nullptr;
			current_scope = item_scope;
		}
		return scopes;
	}

	// No particularly good way to return a reference to an item together with its attributes, so return a vector of
	// item names and look them up in build_response_list_items().
	std::vector<std::string> perform_list_items(bool all, const std::string &scope) {
		std::vector<std::string> item_names;
		for (auto &item : debug_items.table)
			if (all ||
					(scope.empty() && item.first.find(' ') == std::string::npos) ||
					(!scope.empty() && item.first.find(' ') != std::string::npos &&
					 item.first.substr(0, item.first.rfind(' ')) == scope))
				item_names.push_back(item.first);
		return item_names;
	}

	void perform_reference_items(const std::string &name, bool erase, const std::vector<std::tuple<std::string, size_t, size_t>> &designators) {
		references.erase(name);
		if (erase)
			return;
		reference &reference = references[name];
		for (auto &designator : designators) {
			std::string part_name;
			size_t first_index, last_index;
			std::tie(part_name, first_index, last_index) = designator;

			const std::vector<debug_item> &item_parts = debug_items.at(part_name);
			CXXRTL_ASSERT(item_parts.size() == 1 && "Multipart items are not supported yet"); // TODO: not implemented

			const debug_item &item_part = item_parts.at(0);
			CXXRTL_ASSERT(first_index < item_part.depth && last_index < item_part.depth);

			reference.variables.push_back(variable {
				item_part.width,
				(item_part.width + sizeof(chunk_t) * 8 - 1) / (sizeof(chunk_t) * 8),
				item_part.curr,
				first_index,
				last_index,
			});
			if (item_part.outline)
				reference.outlines.insert(item_part.outline);
		}
	}

	// This function is unusual in that it returns a JSON object rather than some other representation. The replies
	// to the `query_interval` command are by far the biggest, so avoiding overhead here is most important.
	json perform_query_interval(const time &begin, const time &end, bool collapse,
															const std::string &items_reference, const std::string &item_values_encoding,
															bool emit_diagnostics) {
		CXXRTL_ASSERT(items_reference.empty() || item_values_encoding == "base64(u32)");

		time timestamp;
		std::vector<diagnostic> diagnostics;

		if (collapse && !emit_diagnostics && player.current_time() == begin && player.get_next_time(timestamp) && timestamp > begin) {
			// In the special case where we need only the item values for a specific point in time, and we're already at that
			// point in time, we don't need to rewind. This massively speeds up repeated examination of the same point in time, as well
			// as stepping forward, regardless of when the last complete checkpoint was.
		} else {
			bool rewound = player.rewind_to_or_before(begin, emit_diagnostics ? &diagnostics : nullptr);
			assert(rewound);
		}

		json samples = json::array();
		std::vector<uint32_t> item_values; // reuse the buffer
		while (true) {
			if (collapse) {
				// Replay all following steps with the same timestamp as the current one. This avoids wasting bandwidth if
				// the client does not have any way to display distinct delta cycles.
				while (player.get_next_time(timestamp) && player.current_time() == timestamp) {
					bool replayed = player.replay(emit_diagnostics ? &diagnostics : nullptr);
					assert(replayed);
				}
			}

			json &sample = samples.emplace_back();
			sample["time"] = player.current_time();

			struct : public performer {
				json *diagnostics = nullptr;

				json build_diagnostic(const std::string &type, const std::string &text, const metadata_map &attrs) {
					json src;
					if (attrs.find("src") != attrs.end() && attrs.at("src").value_type == metadata::STRING)
						src = attrs.at("src").string_value;
					return json {
						{"type", type},
						{"text", text},
						{"src", src},
					};
				}

				void on_print(const lazy_fmt &formatter, const metadata_map &attributes) {
					if (!diagnostics)
						return;
					diagnostics->push_back(build_diagnostic("print", formatter(), attributes));
				}

				void on_check(flavor type, bool condition, const lazy_fmt &formatter, const metadata_map &attributes) {
					if (!diagnostics)
						return;
					if (type == flavor::ASSERT && !condition)
							diagnostics->push_back(build_diagnostic("assert", formatter(), attributes));
					if (type == flavor::ASSUME && !condition)
							diagnostics->push_back(build_diagnostic("assume", formatter(), attributes));
				}
			} performer;

			if (emit_diagnostics) {
				sample["diagnostics"] = json::array();
				for (auto &diagnostic : diagnostics) {
					std::string type;
					switch (diagnostic.type) {
						case diagnostic::BREAK: type = "break"; break;
						case diagnostic::PRINT: type = "print"; break;
						case diagnostic::ASSERT: type = "assert"; break;
						case diagnostic::ASSUME: type = "assume"; break;
					}
					sample["diagnostics"].push_back(json {
						{"type", type},
						{"text", diagnostic.message},
						{"src", diagnostic.location},
					});
				}
				performer.diagnostics = &sample["diagnostics"];
			}

			// Evaluate: calculate values of all non-debug items and emit diagnostics.
			toplevel.eval(&performer);

			if (references.count(items_reference)) {
				auto &reference = references[items_reference];
				for (auto outline : reference.outlines)
					outline->eval();
				if (item_values_encoding == "base64(u32)") {
					item_values.clear();
					for (auto &var : references[items_reference].variables) {
						size_t index = var.first_index;
						while (true) {
							size_t chunk_at = item_values.size();
							item_values.resize(chunk_at + var.chunks);
							std::copy(&var.data[var.chunks * index], &var.data[var.chunks * (index + 1)], &item_values[chunk_at]);
							if (var.width % (sizeof(chunk_t) * 8) != 0) {
								// Sometimes, CXXRTL will leave junk in the value padding bits to save an instruction or two. Clear it.
								item_values[chunk_at + var.chunks - 1] &=
									chunk_t(-1) >> (sizeof(chunk_t) * 8 - (var.width % (sizeof(chunk_t) * 8)));
							}
							if (index == var.last_index)
								break;
							index += (var.first_index < var.last_index ? 1 : -1);
						}
					}
					sample["item_values"] = base64_encode((const char *)&*item_values.begin(), item_values.size() * sizeof(chunk_t));
				}
			}

			// Make sure to not advance past the end of the interval, to speed up repeated examinations of the same point in time.
			if (!player.get_next_time(timestamp) || timestamp > end)
				break;

			diagnostics.clear();
			bool replayed = player.replay(emit_diagnostics ? &diagnostics : nullptr);
			assert(replayed);
		}
		return samples;
	}

	void perform_get_simulation_status(simulation_status &status, time &latest_time, time &next_sample_time) {
		std::unique_lock<std::mutex> lock(shared_state.mutex);
		status = shared_state.status;
		latest_time = shared_state.latest_time;
		next_sample_time = shared_state.next_sample_time;
	}

	bool perform_run_simulation(time until_time, uint32_t until_diagnostics, bool sample_item_values) {
		std::unique_lock<std::mutex> lock(shared_state.mutex);
		if (shared_state.status != simulation_status::paused)
			return false;
		shared_state.run_until_time = until_time;
		shared_state.run_until_diagnostics = until_diagnostics;
		emit_simulation_paused = (until_time < time::maximum() || until_diagnostics != 0);
		CXXRTL_ASSERT(sample_item_values); // TODO: not implemented
		shared_state.unpause = true;
		shared_state.condvar.notify_all();
		shared_state.condvar.wait(lock, [&] { return shared_state.unpause == false; });
		return true;
	}

	time perform_pause_simulation() {
		std::unique_lock<std::mutex> lock(shared_state.mutex);
		shared_state.run_until_time = time();
		shared_state.condvar.notify_all();
		shared_state.condvar.wait(lock, [&] { return shared_state.status != simulation_status::running; });
		return shared_state.latest_time;
	}

	// Wrappers for sending and receiving JSON values.

	json recv() {
		std::string raw_packet = link.recv();
		if (raw_packet.empty())
			return json(nullptr);
#ifdef CXXRTL_SERVER_TRACE
		fprintf(stderr, "C>S: %s\n", raw_packet.c_str());
#endif
		json parsed = json::parse(raw_packet, /*cb=*/nullptr, /*allow_exceptions=*/false);
		return parsed;
	}

	void send(json packet) {
		std::string raw_packet = packet.dump();
#ifdef CXXRTL_SERVER_TRACE
		fprintf(stderr, "S>C: %s\n", raw_packet.c_str());
#endif
		link.send(raw_packet);
	}

	// Parsers and builders for message framings.

	json parse_packet(json &packet, std::string &type) {
		if (packet.is_discarded())
			return build_error("invalid_json", "The received JSON could not be parsed.");
		if (!packet.contains("type"))
			return build_error("invalid_packet", "The received packet does not contain a `type` key.");
		packet.at("type").get_to(type);
		packet.erase("type");
		return json();
	}

	json parse_greeting(json &packet) {
		if (!(packet.contains("version")))
			return build_error("invalid_greeting", "The greeting does not contain a `version` key.");
		if (!(packet.at("version") == 0))
			return build_error("unknown_version", "The client version is not 0.");
		return json();
	}

	json build_greeting() {
		return json {
			{"type", "greeting"},
			{"version", 0},
			{"commands", json::array({
				"list_scopes",
				"list_items",
				"reference_items",
				"query_interval",
				"get_simulation_status",
				"run_simulation",
				"pause_simulation"
			})},
			{"events", json::array({
				"simulation_paused",
				"simulation_finished",
			})},
			{"features", json::object({
				{"item_values_encoding", json::array({"base64(u32)"})}
			})}
		};
	}

	json parse_command(json &packet, std::string &name) {
		if (!(packet.contains("command") && packet.at("command").is_string()))
			return build_error("invalid_command", "The received command does not contain a `command` key.");
		packet.at("command").get_to(name);
		packet.erase("command");
		return json();
	}

	json build_response(std::string command_name, json &&arguments = json()) {
		arguments["type"] = "response";
		arguments["command"] = command_name;
		return arguments;
	}

	json build_error(std::string name, std::string message, json &&arguments = json()) {
		arguments["type"] = "error";
		arguments["error"] = name;
		arguments["message"] = message;
		return arguments;
	}

	json build_event(std::string name, json &&arguments = json()) {
		arguments["type"] = "event";
		arguments["event"] = name;
		return arguments;
	}

	// Helpers for commands and responses.

	json build_attributes(const metadata_map &attrs) {
		json desc_attrs = json::object();
		for (auto &attr : attrs) {
			if (attr.first == "src")
				continue;
			json &desc_attr = (desc_attrs[attr.first] = json::object());
			switch (attr.second.value_type) {
				char buffer[128];
				case metadata::UINT:
					snprintf(buffer, sizeof(buffer), "%" PRIu64, attr.second.uint_value);
					desc_attr["type"] = "unsigned_int";
					desc_attr["value"] = buffer;
					break;
				case metadata::SINT:
					snprintf(buffer, sizeof(buffer), "%+" PRId64, attr.second.uint_value);
					desc_attr["type"] = "signed_int";
					desc_attr["value"] = attr.second.sint_value;
					break;
				case metadata::STRING:
					desc_attr["type"] = "string";
					desc_attr["value"] = attr.second.string_value;
					break;
				case metadata::DOUBLE:
					desc_attr["type"] = "double";
					desc_attr["value"] = attr.second.double_value;
					break;
				case metadata::MISSING:
					// Should never happen.
					continue;
			}
		}
		return desc_attrs;
	}

	// Parsers for commands and builders for responses.

	json parse_command_list_scopes(json &packet, bool &all, std::string &scope) {
		if (!(packet.contains("scope") && (packet.at("scope").is_null() || packet.at("scope").is_string())))
			return build_error("invalid_args", "The `list_scopes` command requires the `scope` argument to be `null` or a string.");
		all = packet.at("scope").is_null();
		if (!all)
			packet.at("scope").get_to(scope);
		packet.erase("scope");
		if (!packet.empty())
			return build_error("invalid_args", "The `list_scopes` command takes no arguments besides `scope`.");
		return json();
	}

	json build_response_list_scopes(const std::map<std::string, const debug_scope*> &scopes) {
		json scope_descs = json::object();
		for (auto &it : scopes) {
			json &scope_desc = (scope_descs[it.first] = json {
				{"type", "module"},
				{"definition", {
					{"name", nullptr},
					{"src", nullptr},
					{"attributes", json::object()}
				}},
				{"instantiation", {
					{"src", nullptr},
					{"attributes", json::object()}
				}}
			});
			// Scopes may be lost. This shouldn't normally happen, but may be the case when using flattened `*.il` files
			// generated with old versions of Yosys, due to bugs in `flatten` pass, etc.
			if (const debug_scope *scope = it.second) {
				const metadata_map &module_attrs = scope->module_attrs->map;
				const metadata_map &cell_attrs = scope->cell_attrs->map;
				scope_desc["definition"]["attributes"] = build_attributes(module_attrs);
				scope_desc["instantiation"]["attributes"] = build_attributes(cell_attrs);
				if (module_attrs.find("src") != module_attrs.end() && module_attrs.at("src").value_type == metadata::STRING)
					scope_desc["definition"]["src"] = module_attrs.at("src").string_value;
				if (cell_attrs.find("src") != cell_attrs.end() && cell_attrs.at("src").value_type == metadata::STRING)
					scope_desc["instantiation"]["src"] = cell_attrs.at("src").string_value;
				scope_desc["definition"]["name"] = scope->module_name;
			}
		}
		return build_response("list_scopes", json {
			{"scopes", scope_descs}
		});
	}

	json parse_command_list_items(json &packet, bool &all, std::string &scope) {
		if (!(packet.contains("scope") && (packet.at("scope").is_null() || packet.at("scope").is_string())))
			return build_error("invalid_args", "The `list_items` command requires the `scope` argument to be `null` or a string.");
		all = packet.at("scope").is_null();
		if (!all)
			packet.at("scope").get_to(scope);
		packet.erase("scope");
		if (!packet.empty())
			return build_error("invalid_args", "The `list_items` command takes no arguments besides `scope`.");
		return json();
	}

	json build_response_list_items(const std::vector<std::string> &item_names) {
		json item_descs = json::object();
		for (auto &item_name : item_names) {
			auto &parts = debug_items.table.at(item_name);
			auto &attrs = debug_items.attrs_table.at(item_name)->map;
			json &item_desc = (item_descs[item_name] = json::object());
			if (attrs.find("src") != attrs.end() && attrs.at("src").value_type == metadata::STRING)
				item_desc["src"] = attrs.at("src").string_value;
			else
				item_desc["src"] = nullptr;
			if (parts.front().type == debug_item::MEMORY) {
				item_desc["type"] = "memory";
				item_desc["lsb_at"] = parts.front().lsb_at;
				item_desc["width"] = parts.back().lsb_at + parts.back().width - parts.front().lsb_at;
				item_desc["zero_at"] = parts.front().zero_at;
				item_desc["depth"] = parts.front().depth;
				// We don't distinguish ROMs in any way at the moment. In addition, a ROM is still useful to be able to set
				// to e.g. update the ROM-resident program. (How does this interact with optimizations? Does Yosys define it?)
				item_desc["settable"] = true;
			} else {
				item_desc["type"] = "node";
				item_desc["lsb_at"] = parts.front().lsb_at;
				item_desc["width"] = parts.back().lsb_at + parts.back().width - parts.front().lsb_at;
				item_desc["input"] = ((parts.front().flags & debug_item::INPUT) != 0);
				item_desc["output"] = ((parts.front().flags & debug_item::OUTPUT) != 0);
				// NOTE: This may not always be correct. Not all inputs deep within hierarchy (determined by the scope name) are
				// undriven because there could have been a prefixed scope (such as "bench "); not all undriven inputs remain
				// undriven when the simulation is composed out of multiple units. The best way to compute the set of settable
				// inputs remains unclear, and this is just a first approximation until we have something better.
				bool settable = false;
				for (auto part : parts) {
					if ((part.flags & debug_item::DRIVEN_SYNC) ||
							((part.flags & debug_item::UNDRIVEN) && (part.flags & debug_item::INPUT)))
						settable = true;
				}
				item_desc["settable"] = settable;
			}
			item_desc["attributes"] = build_attributes(attrs);
		}
		return build_response("list_items", json {
			{"items", item_descs}
		});
	}

	json parse_command_reference_items(json &packet, std::string &reference, bool &erase, std::vector<std::tuple<std::string, size_t, size_t>> &designators) {
		if (!(packet.contains("reference") && (packet.at("reference").is_null() || (packet.at("reference").is_string() && packet.at("reference") != ""))))
			return build_error("invalid_args", "The `reference_items` command requires the `reference` argument to be a non-empty string.");
		reference = packet.at("reference").get<std::string>();
		packet.erase("reference");
		if (!(packet.contains("items") && (packet.at("items").is_null() || packet.at("items").is_array())))
			return build_error("invalid_args", "The `reference_items` command requires the `items` argument to be an array or null.");
		erase = packet.at("items").is_null();
		for (auto json_desig : packet.at("items")) {
			if (!(json_desig.is_array() &&
						(json_desig.size() == 1 || json_desig.size() == 3) &&
						(json_desig[0].is_string()) &&
						(json_desig.size() == 1 || (json_desig[1].is_number_integer() && json_desig[2].is_number_integer()))))
				return build_error("invalid_args", "The `reference_items` command requires the item designator to be an array of a single string, or a string and two integers.");
			std::string item_name = json_desig[0].get<std::string>();
			if (!debug_items.count(item_name))
				return build_error("item_not_found", "The item `" + item_name + "` is not present in the simulation.");
			if (json_desig.size() == 3) {
				if (!debug_items.is_memory(item_name))
					return build_error("wrong_item_type", "The item `" + item_name + "` is referenced as a memory but is a node.");
				designators.emplace_back(item_name, json_desig[1].get<size_t>(), json_desig[2].get<size_t>());
			} else {
				if (debug_items.is_memory(item_name))
					return build_error("wrong_item_type", "The item `" + item_name + "` is referenced as a node but is a memory.");
				designators.emplace_back(item_name, 0, 0);
			}
		}
		packet.erase("items");
		if (!packet.empty())
			return build_error("invalid_args", "The `reference_items` command takes no arguments besides `reference` and `items`.");
		return json();
	}

	json parse_command_query_interval(json &packet, time &begin, time &end, bool &collapse,
																	std::string &items_reference, std::string &item_values_encoding,
																	bool &diagnostics) {
		if (!(packet.contains("interval") && packet.at("interval").is_array() && packet.at("interval").size() == 2))
			return build_error("invalid_args", "The `query_interval` command requires the `interval` argument to be an array of two strings.");
		if (!begin.parse(packet.at("interval").at(0).get<std::string>()))
				return build_error("invalid_args", "The begin time point has incorrect format.");
		if (!end.parse(packet.at("interval").at(1).get<std::string>()))
				return build_error("invalid_args", "The end time point has incorrect format.");
		packet.erase("interval");
		if (!(packet.contains("collapse") && packet.at("collapse").is_boolean()))
			return build_error("invalid_args", "The `query_interval` command requires the `collapse` argument to be a boolean.");
		packet.at("collapse").get_to(collapse);
		packet.erase("collapse");
		if (!(packet.contains("items") && ((packet.at("items").is_string() && packet.at("items") != "") || packet.at("items").is_null())))
			return build_error("invalid_args", "The `query_interval` command requires the `items` argument to be a non-empty string or null.");
		if (!(packet.at("items").is_null() || (packet.at("items").is_string() && references.count(packet.at("items")) != 0)))
			return build_error("invalid_reference", "The reference passed to the `query_interval` command does not exist.");
		if (!packet.at("items").is_null())
			packet.at("items").get_to(items_reference);
		packet.erase("items");
		if (!(packet.contains("item_values_encoding") && (packet.at("item_values_encoding").is_string() || packet.at("item_values_encoding").is_null())))
			return build_error("invalid_args", "The `query_interval` command requires the `item_values_encoding` argument to be a string or null.");
		if (!(packet.at("item_values_encoding").is_null() || packet.at("item_values_encoding") == "base64(u32)"))
			return build_error("invalid_item_values_encoding", "The only supported item values encoding is `base64(u32)`.");
		if (!packet.at("item_values_encoding").is_null())
			packet.at("item_values_encoding").get_to(item_values_encoding);
		packet.erase("item_values_encoding");
		if (!(packet.contains("diagnostics") && packet.at("diagnostics").is_boolean()))
			return build_error("invalid_args", "The `query_interval` command requires the `diagnostics` argument to be a boolean.");
		packet.at("diagnostics").get_to(diagnostics);
		packet.erase("diagnostics");
		if (!packet.empty())
			return build_error("invalid_args", "The `query_interval` command takes no arguments besides `range`, `collapse`, `items`, `item_values_encoding`, and `diagnostics`.");
		return json();
	}

	json build_response_get_simulation_status(simulation_status status, const time &latest_time, const time &next_sample_time) {
		json args = json::object();
		if (status == simulation_status::running) {
			args["status"] = "running";
		} else if (status == simulation_status::paused) {
			args["status"] = "paused";
			args["next_sample_time"] = next_sample_time;
		} else if (status == simulation_status::finished) {
			args["status"] = "finished";
		}
		args["latest_time"] = latest_time;
		return build_response("get_simulation_status", std::move(args));
	}

	json parse_command_run_simulation(json &packet, time &until_time, uint32_t &until_diagnostics, bool &sample_item_values) {
		if (!(packet.contains("until_time") && (packet.at("until_time").is_null() || packet.at("until_time").is_string())))
			return build_error("invalid_args", "The `run_simulation` command requires the `until_time` argument to be null or a string.");
		if (packet.at("until_time").is_null()) {
			until_time = time::maximum();
		} else {
			if (!until_time.parse(packet.at("until_time").get<std::string>()))
				return build_error("invalid_args", "The time point has incorrect format.");
		}
		packet.erase("until_time");
		if (!(packet.contains("until_diagnostics") && packet.at("until_diagnostics").is_array()))
			return build_error("invalid_args", "The `run_simulation` command requires the `until_diagnostics` argument to be an array.");
		until_diagnostics = 0;
		for (json &json_diagnostic_type : packet.at("until_diagnostics"))
			if (json_diagnostic_type == "break")
				until_diagnostics |= (uint32_t)diagnostic_type::breakpoint;
			else if (json_diagnostic_type == "print")
				until_diagnostics |= (uint32_t)diagnostic_type::print;
			else if (json_diagnostic_type == "assert")
				until_diagnostics |= (uint32_t)diagnostic_type::assertion;
			else if (json_diagnostic_type == "assume")
				until_diagnostics |= (uint32_t)diagnostic_type::assumption;
			else
				return build_error("invalid_args", "The `run_simulation` command supports the following diagnostic types: `break`, `print`, `assert`, `assume`.");
		packet.erase("until_diagnostics");
		if (!(packet.contains("sample_item_values") && packet.at("sample_item_values").is_boolean()))
			return build_error("invalid_args", "The `run_simulation` command requires the `sample_item_values` argument to be a boolean.");
		packet.at("sample_item_values").get_to(sample_item_values);
		packet.erase("sample_item_values");
		if (!packet.empty())
			return build_error("invalid_args", "The `run_simulation` command takes no arguments besides `until_time`, `until_diagnostics`, and `sample_item_values`.");
		return json();
	}

	json build_response_pause_simulation(const time &time) {
		return build_response("pause_simulation", json {
			{"time", time}
		});
	}

	json build_event_simulation_paused(const time &time, const std::string &cause) {
		return build_event("simulation_paused", json {
			{"time", time},
			{"cause", cause},
		});
	}

	json build_event_simulation_finished(const time &time) {
		return build_event("simulation_finished", json {
			{"time", time}
		});
	}

	// Main packet processor.

	json process_packet(json &packet) {
		json error;
		std::string type;
		if ((error = parse_packet(packet, type)) != nullptr)
			return error;
		if (type == "greeting") {
			if ((error = parse_greeting(packet)) != nullptr)
				return error;
			got_greeting = true;
			return build_greeting();
		} else if (type == "command") {
			if (!got_greeting)
				return build_error("protocol_error", "A command was received before greetings were exchanged.");
			std::string command;
			if ((error = parse_command(packet, command)) != nullptr)
				return error;
			if (command == "list_scopes") {
				bool all;
				std::string scope;
				if ((error = parse_command_list_scopes(packet, all, scope)) != nullptr)
					return error;
				auto scopes = perform_list_scopes(all, scope);
				return build_response_list_scopes(scopes);
			} else if (command == "list_items") {
				bool all;
				std::string scope;
				if ((error = parse_command_list_items(packet, all, scope)) != nullptr)
					return error;
				auto item_names = perform_list_items(all, scope);
				return build_response_list_items(item_names);
			} else if (command == "reference_items") {
				std::string reference;
				bool erase;
				std::vector<std::tuple<std::string, size_t, size_t>> designators;
				if ((error = parse_command_reference_items(packet, reference, erase, designators)) != nullptr)
					return error;
				perform_reference_items(reference, erase, designators);
				return build_response("reference_items");
			} else if (command == "query_interval") {
				time begin, end;
				bool collapse;
				std::string items_reference;
				std::string item_values_encoding;
				bool emit_diagnostics;
				if ((error = parse_command_query_interval(packet, begin, end, collapse, items_reference, item_values_encoding, emit_diagnostics)) != nullptr)
					return error;
				json samples = perform_query_interval(begin, end, collapse, items_reference, item_values_encoding, emit_diagnostics);
				return build_response("query_interval", json {
					{"samples", samples}
				});
			} else if (command == "get_simulation_status") {
				if (!packet.empty())
					return build_error("invalid_args", "The `get_simulation_status` command takes no arguments.");
				simulation_status status;
				time latest_time, next_sample_time;
				perform_get_simulation_status(status, latest_time, next_sample_time);
				return build_response_get_simulation_status(status, latest_time, next_sample_time);
			} else if (command == "run_simulation") {
				time until_time;
				uint32_t until_diagnostics;
				bool sample_item_values;
				if ((error = parse_command_run_simulation(packet, until_time, until_diagnostics, sample_item_values)) != nullptr)
					return error;
				if (!perform_run_simulation(until_time, until_diagnostics, sample_item_values))
					return build_error("invalid_status", "Cannot run simulation with the current status.");
				return build_response("run_simulation");
			} else if (command == "pause_simulation") {
				if (!packet.empty())
					return build_error("invalid_args", "The `pause_simulation` command takes no arguments.");
				time time = perform_pause_simulation();
				return build_response_pause_simulation(time);
			} else {
				return build_error("invalid_command", "The received command has an unrecognized name.");
			}
		} else {
			return build_error("invalid_packet", "The received packet has an unrecognized type.");
		}
	}

	server(agent_server_state &shared_state, spool &&spool, LinkT &&link = LinkT(), std::string top_path = "")
		: shared_state(shared_state), link(std::move(link)), player(spool) {
		assert(top_path.empty() || top_path.back() == ' ');
		toplevel.debug_info(&debug_items, &debug_scopes, top_path);
		player.start(debug_items);
	}

	server(const server &) = delete;
	server(server &&) = delete;
	server &operator=(const server &) = delete;

	void run() {
		// Handle packets forever unless an I/O error occurs.
		while (link.poll(/*timeout_ms=*/200)) {
			// While there are packets in the receive buffer, parse and process them.
			// A processed packet immediately results in a reply packet; errors, if any, are reported in the reply packet.
			json packet;
			while (!((packet = recv()) == nullptr)) // A parse error value (discarded) is neither == nullptr nor != nullptr.
				send(process_packet(packet));
			// Check if an event should be emitted.
			{
				std::unique_lock<std::mutex> lock(shared_state.mutex);
				if (emit_simulation_paused && shared_state.status == simulation_status::paused) {
					emit_simulation_paused = false;
					switch (shared_state.cause) {
						case pause_reason::time:
							send(build_event_simulation_paused(shared_state.latest_time, "until_time"));
							break;
						case pause_reason::diagnostic:
							send(build_event_simulation_paused(shared_state.latest_time, "until_diagnostics"));
							break;
					}
				}
				if (emit_simulation_finished && shared_state.status == simulation_status::finished) {
					emit_simulation_finished = false;
					send(build_event_simulation_finished(shared_state.latest_time));
				}
			}
		}
		fprintf(stderr, "CXXRTL server encountered an I/O error '%s'; exiting.\n", link.poll_error());
	}

public:
	// A helper function used to create and run the server in a new thread.
	static void start(agent_server_state &shared_state, spool &&spool, LinkT &&link, std::string top_path) {
		// Wait until the initial state is available before starting the server.
		{
			std::unique_lock<std::mutex> lock(shared_state.mutex);
			shared_state.condvar.wait(lock, [&] { return shared_state.status != simulation_status::initializing; });
		}
		server(shared_state, std::move(spool), std::move(link), top_path).run();
	}
};

// Simulation agent.
//
// The agent is embedded in the user defined stimulus code and exists to track timeline advancement. It reports current
// simulation time to the server, and checks whether the simulation should be paused or reset according to the server.

template<class ModuleT>
class agent {
	// Simulation state.
	ModuleT &toplevel;
	recorder recorder;

	// Server state.
	spool spool;          // moved into `thread` by `start_debug`
	std::string top_path; // moved into `thread` by `start_debug`
	std::thread thread;   // initialized by `start_debug`
	agent_server_state shared_state;

public:
	agent(class spool &&spool, ModuleT &toplevel, std::string top_path = "")
		: toplevel(toplevel), recorder(spool), spool(std::move(spool)), top_path(top_path) {
		assert(top_path.empty() || top_path.back() == ' ');
		debug_items debug_items;
		toplevel.debug_info(&debug_items, /*scopes=*/nullptr, top_path);
		recorder.start(debug_items);
	}

	agent(const agent &) = delete;
	agent &operator=(const agent &) = delete;

	~agent() {
		{
			std::unique_lock<std::mutex> lock(shared_state.mutex);
			shared_state.status = simulation_status::finished;
			shared_state.condvar.notify_all();
		}
		if (thread.joinable())
			thread.join();
	}

	bool is_debugging() const {
		return thread.get_id() != std::thread::id();
	}

	template<class LinkT = tcp_link>
	std::string start_debugging(LinkT &&link = LinkT()) {
		assert(!is_debugging());
		std::string uri = link.uri();
		shared_state.run_until_time = cxxrtl::time(); // doesn't need synchronization (yet)
		thread = std::thread(&server<LinkT, ModuleT>::start, std::ref(shared_state), std::move(spool), std::move(link), std::move(top_path));
		return uri;
	}

	void advance(const time &delta) {
		std::unique_lock<std::mutex> lock(shared_state.mutex);
		CXXRTL_ASSERT(shared_state.status != simulation_status::initializing &&
			"Must call `agent.step()` once to capture initial state before `agent.advance()`!");
		time advanced_time = recorder.latest_time() + delta;
		if (advanced_time > shared_state.run_until_time) {
			recorder.flush();
			while (advanced_time > shared_state.run_until_time) {
				shared_state.next_sample_time = advanced_time;
				shared_state.status = simulation_status::paused;
				shared_state.cause = pause_reason::time;
				shared_state.condvar.notify_all();
				shared_state.condvar.wait(lock, [&] { return shared_state.unpause == true; });
				shared_state.unpause = false;
			}
			shared_state.status = simulation_status::running;
			shared_state.condvar.notify_all();
		}
		shared_state.latest_time = recorder.advance_time(delta);
	}

	size_t step(performer *performer) {
		struct : public performer {
			performer *next_performer;
			uint32_t diagnostics_emitted = 0;

			void on_print(const lazy_fmt &formatter, const metadata_map &attributes) override {
				diagnostics_emitted |= (uint32_t)diagnostic_type::print;
				next_performer->on_print(formatter, attributes);
			}

			void on_check(flavor type, bool condition, const lazy_fmt &formatter, const metadata_map &attributes) override {
				if (!condition) {
					switch (type) {
						case flavor::ASSERT: diagnostics_emitted |= (uint32_t)diagnostic_type::assertion;  break;
						case flavor::ASSUME: diagnostics_emitted |= (uint32_t)diagnostic_type::assumption; break;

						case flavor::ASSERT_EVENTUALLY:
						case flavor::ASSUME_EVENTUALLY:
						case flavor::COVER:
							break;
					}
				}
				next_performer->on_check(type, condition, formatter, attributes);
			}
		} wrapping_performer;
		wrapping_performer.next_performer = performer;

		size_t deltas = 0;
		std::unique_lock<std::mutex> lock(shared_state.mutex);
		if (shared_state.status == simulation_status::initializing) {
			deltas = toplevel.step(&wrapping_performer);
			recorder.record_complete();
			recorder.flush();
			shared_state.status = simulation_status::running;
			shared_state.condvar.notify_all();
		} else {
			bool converged = false;
			do {
				converged = toplevel.eval(&wrapping_performer);
				deltas++;
			} while (recorder.record_incremental(toplevel) && !converged);
		}
		if (shared_state.run_until_diagnostics & wrapping_performer.diagnostics_emitted) {
			recorder.flush();
			shared_state.next_sample_time = recorder.latest_time();
			shared_state.status = simulation_status::paused;
			shared_state.cause = pause_reason::diagnostic;
			shared_state.condvar.notify_all();
			shared_state.condvar.wait(lock, [&] { return shared_state.unpause == true; });
			shared_state.unpause = false;
			shared_state.status = simulation_status::running;
			shared_state.condvar.notify_all();
		}
		return deltas;
	}

	size_t step() {
		struct : public performer {
			// Same as `performer::on_check`, but does not call `abort()` (which would kill the agent, too).
			void on_check(flavor type, bool condition, const lazy_fmt &formatter, const metadata_map &attributes) override {
				if (type == flavor::ASSERT || type == flavor::ASSUME)
					if (!condition)
						std::cerr << formatter();
			}
		} performer;
		return step(&performer);
	}

	// Usage: `agent.print("<message>", CXXRTL_LOCATION);`
	void print(const std::string &message, const char *file, unsigned line) {
		recorder.record_diagnostic(diagnostic(diagnostic::PRINT, message, file, line));
	}

	// Usage: `agent.breakpoint(CXXRTL_LOCATION);`
	// Usage: `agent.breakpoint("<message>", CXXRTL_LOCATION);`
	// The message will be rendered similar to `breakpoint at <file>:<line>\n<message>`.
	void breakpoint(const char *file, unsigned line) {
		breakpoint("", file, line);
	}
	void breakpoint(const std::string &message, const char *file, unsigned line) {
		recorder.record_diagnostic(diagnostic(diagnostic::BREAK, message, file, line));
	}

	// Usage: `agent.assertion(p_stb.get<bool>(), "strobe must be active", CXXRTL_LOCATION);
	void assertion(bool condition, const std::string &message, const char *file, unsigned line) {
		if (!condition)
			recorder.record_diagnostic(diagnostic(diagnostic::ASSERT, message, file, line));
	}

	// Usage: `agent.assumption(p_count.get<uint32_t>() < 100, "counter must be less than 100", CXXRTL_LOCATION);
	void assumption(bool condition, const std::string &message, const char *file, unsigned line) {
		if (!condition)
			recorder.record_diagnostic(diagnostic(diagnostic::ASSUME, message, file, line));
	}
};

// The contents of this macro may change with no warning or backward compatibility provisions.
// It may also eventually start to differ between builds with different C++ standard versions.
#define CXXRTL_LOCATION __FILE__, __LINE__

}

#endif
