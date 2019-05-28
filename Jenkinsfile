void setBuildStatus(String message, String context, String state) {
    // add a Github access token as a global 'secret text' credential on Jenkins with the id 'github-commit-status-token'
    withCredentials([string(credentialsId: 'github-commit-status-token', variable: 'TOKEN')]) {
      // 'set -x' for debugging. Don't worry the access token won't be actually logged
      // Also, the sh command actually executed is not properly logged, it will be further escaped when written to the log
        sh """
            set -x
            curl \"https://api.github.com/repos/FeatureIDE/FeatureIDE/statuses/$GIT_COMMIT?access_token=$TOKEN\" \
                -H \"Content-Type: application/json\" \
                -X POST \
                -d \"{\\\"description\\\": \\\"$message\\\", \\\"state\\\": \\\"$state\\\", \\\"context\\\": \\\"$context\\\", \\\"target_url\\\": \\\"$BUILD_URL\\\"}\"
        """
    } 
}

pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {
                setBuildStatus("Compiling", "compile", "pending");
                sh '''
                    echo "PATH = ${PATH}"
                    echo "M2_HOME = ${M2_HOME}"
                '''
                setBuildStatus("Build complete", "compile", "success");
            }
        }

        stage ('Test') {
            steps {
                setBuildStatus("Compiling", "compile", "pending");
                sh 'mvn clean test' 
                setBuildStatus("Build complete", "compile", "success");
            }
        }

        stage ('Package') {
        	steps {
                setBuildStatus("Compiling", "compile", "pending");
        		sh 'mvn clean package'
                setBuildStatus("Build complete", "compile", "success");
        	}
        }


        stage ('Verify') {
        	steps {
                setBuildStatus("Compiling", "compile", "pending");
        		sh 'mvn clean verify'
                setBuildStatus("Build complete", "compile", "success");
        	}
        }

    }
}