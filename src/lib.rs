use ansi_term::{ANSIDisplay, Color, Style};
use chrono::{DateTime, Utc};
use lazy_static::lazy_static;

use parse_display::Display;
use rand::RngCore;
use core::error::Error;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io::{BufWriter, ErrorKind, Write};
use std::sync::{Arc, Mutex, RwLock};
use std::time::SystemTime;
use std::{fmt, fs, io, thread};
use std::mem::replace;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::Thread;
use stack_buf_io::StackBufWriter;

lazy_static::lazy_static!{
	static ref ANSI_SUPPORT_ENABLED: bool = {
        #[cfg(target_os = "windows")]
        {
            ansi_term::enable_ansi_support().is_ok()
        }
        #[cfg(not(target_os = "windows"))]
        {
            true
        }
    };
}

fn ansi_support_enabled() -> bool {
	*ANSI_SUPPORT_ENABLED
}

/// Implementors must guarantee that the function received as the first argument is always
/// executed exactly once, no more no less. Failure to uphold this guarantee may result in runtime
/// panics and/or logic errors.
pub type LoggerLookupFunc = fn(&mut dyn FnMut(&Logger));

/// The log filter determines whether a message will be written to an output.
pub trait LogFilter: Send + Sync {
	fn test_message(&self, target: Target, message: &Message) -> bool;

	fn box_clone(&self) -> Box<dyn LogFilter>;
}

#[derive(Copy, Clone)]
pub struct DefaultLogFilter;

impl LogFilter for DefaultLogFilter {
	#[inline]
	fn test_message(&self, target: Target, message: &Message) -> bool {
		match target {
			Target::Stdout => {
				#[cfg(debug_assertions)]
				{
					message.severity >= Severity::Debug
				}
				#[cfg(not(debug_assertions))]
				{
					message.severity >= Severity::Info
				}
			},
			Target::File => message.severity >= Severity::Trace,
		}
	}

	#[inline]
	fn box_clone(&self) -> Box<dyn LogFilter> {
		Box::new(DefaultLogFilter)
	}
}

lazy_static!{
    pub static ref GLOBAL_LOGGER: Logger = {
		extern "C" fn flush_global_logger() {
			GLOBAL_LOGGER.flush();
        }

		shutdown_hooks::add_shutdown_hook(flush_global_logger);
		Logger::new()
	};
}

static LOGGER_LOOKUP_FUNC: RwLock<LoggerLookupFunc> = RwLock::new(always_global);

/// Changes the global logger lookup function, which is executed
/// when using the static log functions of `Logger` or the `log!` macro
/// without a logger as the first parameter
pub fn set_logger_lookup_func(f: LoggerLookupFunc) {
	*LOGGER_LOOKUP_FUNC.write().unwrap() = f;
}

/// Logger lookup function that always invokes the global logger
pub fn always_global(func: &mut dyn FnMut(&Logger)) {
	func(&GLOBAL_LOGGER);
}

#[cfg(feature = "log")]
pub fn initialize() -> Result<(), log::SetLoggerError> {
	use log::{LevelFilter, Metadata, Record};

	struct DynLogger;
	impl log::Log for DynLogger {
		#[inline]
		fn enabled(&self, metadata: &Metadata) -> bool {
			Logger::apply_to_current(|logger| <Logger as log::Log>::enabled(logger, metadata))
		}
		#[inline]
		fn log(&self, record: &Record) {
			Logger::apply_to_current(|logger| <Logger as log::Log>::log(logger, record))
		}
		#[inline]
		fn flush(&self) {
			Logger::apply_to_current(|logger| <Logger as log::Log>::flush(logger))
		}
	}

	log::set_logger(&DynLogger)?;
	log::set_max_level(LevelFilter::Trace); // Because we do our own filtering

	Ok(())
}

#[cfg(feature = "log")]
fn level_to_severity(level: log::Level) -> Severity {
	use log::Level;
	match level {
		Level::Error => Severity::Error,
		Level::Warn => Severity::Warning,
		Level::Info => Severity::Info,
		Level::Debug => Severity::Debug,
		Level::Trace => Severity::Trace
	}
}

const MAX_RECURSION_DEPTH: usize = 256;
const STACK_BUF_SIZE: usize = 512; // This way most log messages will be printed in a single write call
const NEWLINE_MARKER: &str = "\n>";

#[macro_export]
macro_rules! log {
	($severity:ident, $error:expr, $format:literal, $($arg:expr),*) => {{
		$crate::Logger::apply_to_current(|logger| {
			logger.log($crate::Message {
				severity: $crate::Severity::$severity,
				message: ::core::format_args!($format, $($arg),*),
				error: Some(&$error),
				module: Some(::core::module_path!()),
				line: Some(::core::line!()),
			});
		});
	}};
	($severity:ident, $format:literal, $($arg:expr),*) => {{
		$crate::Logger::apply_to_current(|logger| {
			logger.log($crate::Message {
				severity: $crate::Severity::$severity,
				message: ::core::format_args!($format, $($arg),*),
				error: None,
				module: Some(::core::module_path!()),
				line: Some(::core::line!()),
			});
		});
	}};
    ($severity:ident, $error:expr, $format:literal) => {{
		$crate::Logger::apply_to_current(|logger| {
			logger.log($crate::Message {
				severity: $crate::Severity::$severity,
				message: ::core::format_args!($format),
				error: Some(&$error),
				module: Some(::core::module_path!()),
				line: Some(::core::line!()),
			});
		});
	}};
	($severity:ident, $format:literal) => {{
		$crate::Logger::apply_to_current(|logger| {
			logger.log($crate::Message {
				severity: $crate::Severity::$severity,
				message: ::core::format_args!($format),
				error: None,
				module: Some(::core::module_path!()),
				line: Some(::core::line!()),
			});
		});
	}};
	($severity:ident, $error:expr) => {{
		$crate::Logger::apply_to_current(|logger| {
			logger.log($crate::Message {
				severity: $crate::Severity::$severity,
				message: ::core::format_args!(""),
				error: Some(&$error),
				module: Some(::core::module_path!()),
				line: Some(::core::line!()),
			});
		});
	}};
}

#[macro_export]
macro_rules! log_to {
    ($logger:expr, $severity:ident, $error:expr, $format:literal, $($arg:expr),*) => {{
		$logger.log($crate::Message {
			severity: $crate::Severity::$severity,
			message: ::core::format_args!($format, $($arg),*),
			error: Some(&$error),
			module: Some(::core::module_path!()),
			line: Some(::core::line!()),
		});
	}};
	($logger:expr, $severity:ident, $format:literal, $($arg:expr),*) => {{
		$logger.log($crate::Message {
			severity: $crate::Severity::$severity,
			message: ::core::format_args!($format, $($arg),*),
			error: None,
			module: Some(::core::module_path!()),
			line: Some(::core::line!()),
		});
	}};
    ($logger:expr, $severity:ident, $error:expr, $format:literal) => {{
		$logger.log($crate::Message {
			severity: $crate::Severity::$severity,
			message: ::core::format_args!($format),
			error: Some(&$error),
			module: Some(::core::module_path!()),
			line: Some(::core::line!()),
		});
	}};
	($logger:expr, $severity:ident, $format:literal) => {{
		$logger.log($crate::Message {
			severity: $crate::Severity::$severity,
			message: ::core::format_args!($format),
			error: None,
			module: Some(::core::module_path!()),
			line: Some(::core::line!()),
		});
	}};
	($logger:expr, $severity:ident, $error:expr) => {{
		$logger.log($crate::Message {
			severity: $crate::Severity::$severity,
			message: ::core::format_args!(""),
			error: Some(&$error),
			module: Some(::core::module_path!()),
			line: Some(::core::line!()),
		});
	}};
}

#[macro_export]
macro_rules! safe_print {
    ($format:literal, $($arg:expr),*) => {
         write!(io::stdout(), $format, $($arg),*).unwrap_or(());
    };
    ($format:literal) => {
        write!(io::stdout(), $format).unwrap_or(());
    }
}

#[macro_export]
macro_rules! safe_println {
    ($format:literal, $($arg:expr),*) => {
         writeln!(io::stdout(), $format, $($arg),*).unwrap_or(());
    };
    ($format:literal) => {
        writeln!(io::stdout(), $format).unwrap_or(());
    }
}

#[macro_export]
macro_rules! safe_eprint {
    ($format:literal, $($arg:expr),*) => {
         write!(io::stderr(), $format, $($arg),*).unwrap_or(());
    };
    ($format:literal) => {
        write!(io::stderr(), $format).unwrap_or(());
    }
}

#[macro_export]
macro_rules! safe_eprintln {
    ($format:literal, $($arg:expr),*) => {
         writeln!(io::stderr(), $format, $($arg),*).unwrap_or(());
    };
    ($format:literal) => {
        writeln!(io::stderr(), $format).unwrap_or(());
    }
}

struct NewlineReplacer<'a, T: Write>(T, &'a str);

impl<T: Write> Write for NewlineReplacer<'_, T> {
	#[inline]
	fn write(&mut self, mut buf: &[u8]) -> io::Result<usize> {
		let original_len = buf.len();
		loop {
			// Calculate maximum write length before a newline
			let max_uninterrupted = buf
				.iter()
				.enumerate()
				.find_map(|(idx, &value)| if value == '\n' as u8 { Some(idx) } else { None });

			match max_uninterrupted {
				// The maximum writable bytes is zero, that means the slice begins with a newline
				Some(0) => {
					self.0.write_all(self.1.as_bytes())?;

					// Advance by one so that the next iteration goes past the newline
					buf = &buf[1..];
				}
				Some(max) => {
					let writable = &buf[..max];
					self.0.write_all(writable)?;

					buf = &buf[max..];
				},
				// In this case there are no newline characters until the end of the string
				None => {
					self.0.write_all(buf)?;
					break;
				}
			}
		}

		Ok(original_len)
	}

	#[inline]
	fn flush(&mut self) -> io::Result<()> {
		self.0.flush()
	}

	fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
		self.write(buf).map(|_| ())
	}
}

#[derive(Copy, Clone)]
pub struct Message<'a> {
	pub severity: Severity,
	pub message: fmt::Arguments<'a>,
	pub error: Option<&'a dyn Error>,
	pub module: Option<&'a str>,
	pub line: Option<u32>
}

/// Represents the target of a log message, meaning the place the logger is trying to write it to.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub enum Target {
	Stdout,
	File
}

struct PrefixTempData {
	show_thread: bool,
	show_module: bool,
	thread: Thread,
	date: DateTime<Utc>,
	time: SystemTime,
}

impl PrefixTempData {
	fn new(logger: &Logger) -> Self {
		Self {
			show_thread: logger.show_thread.load(Ordering::Acquire),
			show_module: logger.show_module.load(Ordering::Relaxed),
			thread: thread::current(),
			date: Utc::now(),
			time: SystemTime::now(),
		}
	}
}

/// Represents the severity of a logger message,
/// and it will be displayed and used to determine
/// if a message should be printed or not
#[derive(Copy, Clone, Eq, PartialEq, PartialOrd, Debug, Display)]
#[repr(usize)]
#[non_exhaustive]
pub enum Severity {
	Trace,
	Debug,
	Info,
	Loading,
	Warning,
	Error,
	Fatal,
}

impl Severity {
	#[inline]
	pub fn style(&self) -> Style {
		match self {
			Severity::Trace => Color::Blue.bold(),
			Severity::Debug => Color::Green.bold(),
			Severity::Info => Color::Cyan.bold(),
			Severity::Loading => Color::Purple.bold(),
			Severity::Warning => Color::Yellow.bold(),
			Severity::Error => Color::Red.bold(),
			Severity::Fatal => {
				let mut style = Style::new();
				style.is_bold = true;
				style.foreground = Some(Color::Red);
				style.background = Some(Color::Yellow);
				style
			}
		}
	}

	#[inline]
	pub fn styled(&self) -> ANSIDisplay<'_, Self> {
		self.style().paint(self)
	}
}

struct SharedLoggerData {
	attempt_creation: bool,
	log_file: Option<Box<dyn Write + Send>>,
}

impl SharedLoggerData {
	fn new() -> Self {
		Self {
			attempt_creation: true,
			log_file: None,
		}
	}
}

#[derive(Debug, Clone)]
struct PrefixData {
	string: String,
	color: Color
}

impl PrefixData {
	#[inline]
	pub fn style(&self) -> Style {
		self.color.normal()
	}

	#[inline]
	fn styled(&self) -> ANSIDisplay<'_, Self> {
		self.style().paint(self)
	}
}

impl fmt::Display for PrefixData {
	#[inline]
	fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.string)
	}
}

/// A logger allows you to print messages to stdout in a
/// standardized way while also optionally logging them to a file
///
/// Unlike the print macro, a logger will not panic on an error but rather
/// ignore it and, if the error happens while writing to a file, close the handle
pub struct Logger {
	shared: Arc<Mutex<SharedLoggerData>>,
	prefix: Vec<PrefixData>,
	filter: RwLock<Box<dyn LogFilter>>,
	show_thread: AtomicBool,
	show_module: AtomicBool,
}

impl Clone for Logger {
	#[inline]
	fn clone(&self) -> Self {
		Self {
			shared: self.shared.clone(),
			prefix: self.prefix.clone(),
			filter: RwLock::new(self.filter.read().unwrap().box_clone()),
			show_thread: AtomicBool::new(self.show_thread.load(Ordering::Acquire)),
			show_module: AtomicBool::new(self.show_module.load(Ordering::Acquire)),
		}
	}
}

impl Logger {
	/// Creates a new logger
	///
	/// # Returns
	/// * A new logger
	#[inline]
	pub fn new() -> Self {
		Self {
			shared: Arc::new(Mutex::new(SharedLoggerData::new())),
			prefix: Vec::new(),
			filter: RwLock::new(Box::new(DefaultLogFilter)),
			show_thread: AtomicBool::new(true),
			show_module: AtomicBool::new(true),
		}
	}

	/// Creates a new logger that shares the log file with a different logger
	///
	/// # Returns
	/// * A new logger
	#[inline]
	pub fn new_with_log_file(other: &Logger) -> Self {
		Self {
			shared: other.shared.clone(),
			prefix: Vec::new(),
			filter: RwLock::new(Box::new(DefaultLogFilter)),
			show_thread: AtomicBool::new(true),
			show_module: AtomicBool::new(true),
		}
	}

	/// Logs a message.
	///
	/// # Arguments
	/// * `message` - The message to print
	#[inline]
	pub fn log(&self, message: Message) {
		let filter = self.filter.read().unwrap();

		if filter.test_message(Target::Stdout, &message) {
			self.write_std(message);
		}

		if filter.test_message(Target::File, &message) {
			let mut data = self.shared.lock().unwrap();

			// Only if we have no output device...
			if data.log_file.is_none() && replace(&mut data.attempt_creation, false) {
				self.create_log_file(&mut data);
			}

			self.write_file(&mut data, message);
		}
	}

	#[inline]
	pub fn set_filter<F>(&self, filter: F)
	where F: Fn(Target, &Message) -> bool + Send + Sync + Clone + 'static
	{
		#[repr(transparent)]
		#[derive(Clone)]
		struct Filter<T>(T)
		where T: Fn(Target, &Message) -> bool + Send + Sync + Clone + 'static;

		impl<T> LogFilter for Filter<T>
		where T: Fn(Target, &Message) -> bool + Send + Sync + Clone + 'static
		{
			#[inline]
			fn test_message(&self, target: Target, message: &Message) -> bool {
				self.0(target, message)
			}

			#[inline]
			fn box_clone(&self) -> Box<dyn LogFilter> {
				Box::new(self.clone())
			}
		}

		*self.filter.write().unwrap() = Box::new(Filter(filter));
	}

	fn create_log_file(&self, data: &mut SharedLoggerData) {
		// Try to create a logs folder
		match fs::create_dir_all("logs") {
			Ok(_) => {}
			Err(error) => {
				safe_eprintln!("Error while creating folder structure for log files: {}", Self::gen_error_str(&error));
				return;
			}
		}
		let date = Utc::now();

		// Base file name
		let name = format!("logs/{}.log", date.format("%d_%m_%Y_%H_%M"));
		let mut name2: String;
		let mut log_file_result = File::create_new(&name);

		// Keep trying increasing log file indexes until we find a free file name
		let mut number: usize = 0;
		while let Err(err) = &log_file_result && let ErrorKind::AlreadyExists = err.kind() {
			number += 1;
			name2 = format!("logs/{}_{}.log", date.format("%d_%m_%Y_%H_%M"), number);

			log_file_result = File::create_new(&name2);
		}

		match log_file_result {
			Ok(file) => {
				// Update the log file
				data.log_file = Some(Box::new(BufWriter::new(file)));
			}
			Err(error) => {
				data.log_file = None;
				safe_eprintln!("Error while creating log file: {}", Self::gen_error_str(&error));
			}
		}
	}

	fn write_std(&self, message: Message) {
		if message.severity >= Severity::Error {
			let _ = self.do_write(&mut StackBufWriter::<_, STACK_BUF_SIZE>::new(io::stderr().lock()), message, ansi_support_enabled());
		} else {
			let _ = self.do_write(&mut StackBufWriter::<_, STACK_BUF_SIZE>::new(io::stdout().lock()), message, ansi_support_enabled());
		}
	}

	fn write_file(
		&self,
		data: &mut SharedLoggerData,
		message: Message
	)
	{
		// Write to the file only if it's open
		if let Some(file) = &mut data.log_file {
			match self.do_write(file, message, false) {
				Err(error) => {
					// Write error, handle is probably dead, invalidate it
					data.log_file = None;

					safe_eprintln!("Cannot write to log file: {}", Self::gen_error_str(&error).as_str());
				}
				_ => {}
			}
		}
	}

	fn write_prefix<T: Write>(&self, device: &mut T, pretty: bool) -> io::Result<()> {
		let mut depth = 0;
		for prefix in self.prefix.iter() {
			if pretty {
				write!(NewlineReplacer(&mut *device, ""), " -> {}", prefix.styled())?;
			} else {
				write!(NewlineReplacer(&mut *device, ""), "[{}]", prefix)?;
			}

			// Failsafe for too many nested loggers
			if depth >= MAX_RECURSION_DEPTH {
				static MSG: &str = "*prefix chain truncated*";
				return if pretty {
					write!(device, " -> {MSG}")
				} else {
					write!(device, "[{MSG}]")
				};
			}
			depth += 1;
		}
		Ok(())
	}

	fn write_complete_prefix<T: Write>(&self, device: &mut T, message: Message, pretty: bool, temp: &PrefixTempData) -> io::Result<()> {
		let thread_name = temp.thread.name().unwrap_or("*unnamed_thread*");

		if pretty {
			write!(device, "{}.{:03}",
				   temp.date.format("%H:%M::%S"),
				   temp.date.timestamp_subsec_millis()
			)?;
		} else {
			write!(
				device,
				"[{}]",
				humantime::format_rfc3339_millis(temp.time)
			)?;
		}

		self.write_prefix(device, pretty)?;

		if pretty {
			if temp.show_thread {
				write!(NewlineReplacer(&mut *device, ""), " -> thread `{}`",
					   thread_name,
				)?;
			}

			if temp.show_module && let Some(module) = message.module {
				let mut style = Style::new();
				style.background = Some(Color::White);
				style.foreground = Some(Color::Black);
				write!(NewlineReplacer(&mut *device, ""), " at {}", style.paint(module))?;

				if let Some(line) = message.line {
					let mut style = Style::new();
					style.background = Some(Color::White);
					style.foreground = Some(Color::Black);
					write!(device, "{}{}", style.paint(":"), style.paint(&line))?;
				}
			}

			write!(device, " -> {}", message.severity.styled())?;
		} else {
			if temp.show_thread {
				write!(NewlineReplacer(&mut *device, ""), "[{}]", thread_name)?;
			}
			if temp.show_module && let Some(module) = message.module {
				write!(NewlineReplacer(&mut *device, ""), "[at {module}")?;

				if let Some(line) = message.line {
					write!(device, ":{line}")?;
				}
				write!(device, "]")?;
			}
			write!(device, "[{}]", message.severity)?;
		}

		write!(device, ": ")
	}

	fn do_write<T: Write>(&self, device: &mut T, message: Message, pretty: bool) -> io::Result<()> {
		let temp = PrefixTempData::new(self);
		if pretty {
			write!(device, "{}", Color::White.normal().paint(""))?; // Reset color
		}
		self.write_complete_prefix(device, message, pretty, &temp)?;

		NewlineReplacer(&mut *device, NEWLINE_MARKER).write_fmt(message.message)?;

		writeln!(device)?;

		// Write errors
		if let Some(error) = message.error {
			self.write_complete_prefix(device, message, pretty, &temp)?;
			if pretty {
				write!(NewlineReplacer(&mut *device, NEWLINE_MARKER), "{}: {}",
				         Color::Red.paint("Error"),
				         error
				)?;
			} else {
				write!(NewlineReplacer(&mut *device, NEWLINE_MARKER), "Error: {}", error)?;
			}
			writeln!(device)?;

			let mut source_option = error.source();
			let mut depth: usize = 0;
			while let Some(source) = source_option {
				if depth >= MAX_RECURSION_DEPTH {
					writeln!(device, "*error chain truncated*")?;
					break;
				}

				self.write_complete_prefix(device, message, pretty, &temp)?;
				if pretty {
					write!(NewlineReplacer(&mut *device, NEWLINE_MARKER), "{}: {}",
					         Color::Yellow.paint("Caused by"),
					         source
					)?;
				} else {
					write!(NewlineReplacer(&mut *device, NEWLINE_MARKER), "Caused by: {}", source)?;
				}
				writeln!(device)?;
				source_option = source.source();

				depth += 1;
			}
		}

		Ok(())
	}

	fn gen_error_str(error: &dyn Error) -> String {
		let mut err_str = format!("Error: {}", error);
		let mut source_option = error.source();
		while let Some(source) = source_option {
			let to_push = format!("\nCaused by: {}", source);
			err_str.push_str(&to_push);
			source_option = source.source();
		}
		err_str
	}

	/// Sets whether an attempt should be made to print information about the current
	/// thread.
	///
	/// Tokio tasks may be supported in the future and this setting will then also refer to that.
	#[inline]
	pub fn set_show_thread(&self, show_thread: bool) {
		self.show_thread.store(show_thread, Ordering::Release);
	}

	/// Sets whether an attempt should be made to print information about the
	/// module path of a message
	#[inline]
	pub fn set_show_module(&self, show_module: bool) {
		self.show_module.store(show_module, Ordering::Release);
	}

	/// Changes the file log messages are written to.
	///
	/// Calling this with any value will prevent automatic log file creation in favor of the
	/// provided output device.
	///
	/// This means that calling this with `None` before logging anything effectively stops any
	/// log file from being created.
	///
	/// # Arguments
	/// * `file` - The new file (or no file)
	#[inline]
	pub fn set_log_output(&self, device: Option<Box<dyn Write + Send>>) {
		let mut data = self.shared.lock().unwrap();
		data.log_file = device;
		data.attempt_creation = false;
	}

	/// Checks if a message would be logged to the console or to a file
	/// with the given severity
	///
	/// # Arguments
	/// * `severity` - The severity to check
	///
	/// # Returns
	/// * Whether a message with such a severity would be logged or ignored
	#[inline]
	pub fn is_enabled(&self, target: Target, message: &Message) -> bool {
		self.filter.read().unwrap().test_message(target, message)
	}

	/// Flushes the log file. This won't flush stdout (unless it was specifically
	/// registered as a log file for some reason)
	#[inline]
	pub fn flush(&self) {
		if let Ok(data) = self.shared.lock() &&
			let Some(ref mut file) = data.log_file {
			match file.flush() {
				Err(error) => {
					// Flush error, handle is probably dead so invalidate it
					data.log_file = None;

					safe_eprintln!("Cannot flush log file: {}", Self::gen_error_str(&error).as_str());
				}
				_ => {}
			}
		}
	}

	/// Creates a sub-logger from this logger.
	///
	/// When printing with the returned logger, it will act
	/// exactly like its parent but will also print
	/// the given prefix and (if pretty printing is supported) color.
	///
	/// Any change done to this logger will reflect on
	/// the parent and vice versa
	///
	/// # Arguments
	/// - `prefix` - The prefix of this logger as a string literal
	/// - `color` - The color used when pretty-printing
	#[inline]
	pub fn sub_logger_colored(&self, prefix: &str, color: Color) -> Self {
		let mut sub_logger = self.clone();
		sub_logger.prefix.push(PrefixData {
			string: prefix.to_owned(),
			color
		});

		sub_logger
	}

	/// Creates a sub-logger from this logger.
	///
	/// When printing with the returned logger, it will act
	/// exactly like its parent but will also print
	/// the given prefix and (if pretty printing is supported) a random color.
	///
	/// Any change done to this logger will reflect on
	/// the parent and vice versa
	///
	/// # Arguments
	/// - `prefix` - The prefix of this logger as a string literal
	#[inline]
	pub fn sub_logger(&self, prefix: &str) -> Self {
		fn rand_color() -> Color {
			const COLORS: [u8; 12] = [
				1, 2, 3, 4, 5 ,6, 9, 10, 11, 12, 13, 14
			];

			let mut rng = rand::rng();
			let idx = rng.next_u32() as usize % COLORS.len();
			Color::Fixed(COLORS[idx])
		}

		self.sub_logger_colored(prefix, rand_color())
	}

	#[inline]
	pub fn apply_to_current<F, R>(f: F) -> R
	where
		F: FnOnce(&Logger) -> R,
	{
		static MSG: &str = "logger lookup function called the logger more than once (or none at all)";
		let lookup = LOGGER_LOOKUP_FUNC.read().unwrap();
		let mut option = Some(f);
		let mut result = None;
		lookup(&mut |logger| {
			result = Some(option.take().expect(MSG)(logger));
		});
		result.expect(MSG)
	}
}

impl Drop for Logger {
	#[inline]
	fn drop(&mut self) {
		if let Ok(mut shared) = self.shared.lock() &&
			let Some(ref mut log_file) = shared.log_file {
			let _ = log_file.flush();
		}
	}
}

#[cfg(feature = "log")]
impl log::Log for Logger {
	#[inline]
	fn enabled(&self, metadata: &log::Metadata) -> bool {
		let severity = level_to_severity(metadata.level());

		self.is_enabled(Target::File, &Message {
			severity,
			message: format_args!(""),
			error: None,
			module: None,
			line: None
		})
	}

	#[inline]
	fn log(&self, record: &log::Record) {
		let severity = level_to_severity(record.level());
		self.log(Message {
			severity,
			message: *record.args(),
			error: None,
			module: record.module_path(),
			line: record.line(),
		});
	}

	#[inline]
	fn flush(&self) {
		self.flush();
	}
}

#[test]
fn test_logger() {
	use thiserror::Error;
	#[derive(Debug, Error, Display)]
	#[display("This is a dummy error message")]
	struct DummyError;

	// This is a compilation test more than anything

	let logger = GLOBAL_LOGGER.sub_logger("TestSubLogger");

	logger.set_filter(|target, message| {
		match target {
			Target::Stdout => message.severity >= Severity::Debug,
			Target::File => message.severity >= Severity::Trace,
		}
	});

	let arg1: bool = false;
	let arg2: i32 = 42;
	let arg3: &str = "HELLO THERE";

	let error = DummyError;

	// Severity, error, literal, format args
	log!(Warning, error, "Formatting: {}, {}, {}", arg1, arg2, arg3);

	// Severity, literal, format args
	log!(Warning, "Another formatting: {}, {}, {}", arg1, arg2, arg3);

	// Severity, error, literal
	log!(Warning, error, "Just a string literal");

	// Severity, literal
	log!(Warning, "Literal with no error");

	// Logger, severity, error, literal, format args
	log_to!(logger, Warning, error, "Formatting: {}, {}, {}", arg1, arg2, arg3);

	// Logger, severity, literal, format args
	log_to!(logger, Warning, "Another formatting: {}, {}, {}", arg1, arg2, arg3);

	// Logger, severity, error, literal
	log_to!(logger, Warning, error, "Just a string literal");

	// Logger, severity, literal
	log_to!(logger, Warning, "Literal with no error");

	// COLORS
	log!(Trace, "Hello");
	log!(Debug, "Hello");
	log!(Info, "Hello");
	log!(Loading, "Hello");
	log!(Warning, "Hello");
	log!(Error, "Hello");
	log!(Fatal, "Hello");

	// Nested loggers
	let mut loggers = Vec::new();
	loggers.push(logger);
	for i in 0..20 {
		let new = loggers.last().unwrap().sub_logger(&format!("sub_{}", i));
		log_to!(new, Info, "Hello");
		loggers.push(new);
	}
}