# Written by Samuel Burns Cohen
#
# check.rb
#
# This program runs unit tests on the Leij interpreter

def parseTest(filename)
  text = File.read(filename)
  description = if match = text.match(/@description: ?(.+)/i)
                then (match.captures)[0] else "no description" end
  return description
end

def evalTest(test, description)
  response = `./bin/lc -q #{test}`
  if response.empty? and $?.exitstatus == 0 then
    puts "#{description} \u001b[32mPASSED\u001b[0m"
  else
    puts ("#{description} \u001b[31mFAILED\u001b[0m\n" + response)
  end
end

if ARGV.size != 1 then
  puts "Usage: ruby check.rb [path to tests directory]"
  exit 1
end

dirPath = ARGV[0];
tests = Dir.glob("#{dirPath}/**/*").select { |e|
  File.file? e and File.extname(e) == ".lj"
};

tests.each do |test|
  description = parseTest test
  evalTest(test, description)
end
