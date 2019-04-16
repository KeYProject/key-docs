pipeline {
  agent {
    docker {
      image 'python'
    }

  }
  stages {
    stage('Check packages') {
      steps {
        sh 'make prepare'
      }
    }
    stage('Build') {
      steps {
        sh 'make build'
      }
    }
    stage('Publish') {
      steps {
        sshPublisher(publishers: [sshPublisherDesc(configName: 'KeY Docs', transfers: [sshTransfer(cleanRemote: false, excludes: '', execCommand: '', execTimeout: 120000, flatten: false, makeEmptyDirs: false, noDefaultExcludes: false, patternSeparator: '[, ]+', remoteDirectory: '/home/docs/www/', remoteDirectorySDF: false, removePrefix: 'site/', sourceFiles: 'site/**')], usePromotionTimestamp: false, useWorkspaceInPromotion: false, verbose: false)])
      }
    }
  }
}